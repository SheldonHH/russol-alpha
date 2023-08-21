use std::{
    path::PathBuf,
    process::{Command, Stdio},
    sync::mpsc::Sender,
    time::{Duration, Instant},
};

use rustc_ast::LitIntType;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_type_ir::{IntTy, UintTy};
use wait_timeout::ChildExt;

use crate::{
    hir_translator::{PureFn, PureFnMap},
    ruslik_types::RuslikFnSig,
    subst_generics::SGenericsCollector,
    suslik_translate::{outlives_relations, ExprTranslator, STyTranslator},
    trait_bounds::find_trait_fns,
};

// 定义一个名为PredMap的类型别名，其为一个基于HashMap的快速哈希映射，键是字符串，值是Predicate类型。
pub type PredMap = FxHashMap<String, Predicate>;

// 定义一个二进制操作的枚举类型，可以是Rust内置的或是SetContains操作
#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Rust(RustBinOp),
    SetContains,
}
impl From<RustBinOp> for BinOp {
    fn from(rust: RustBinOp) -> Self {
        BinOp::Rust(rust)
    }
}
impl From<&RustBinOp> for BinOp {
    fn from(rust: &RustBinOp) -> Self {
        BinOp::Rust(*rust)
    }
}
pub type RustBinOp = rustc_hir::BinOpKind;
pub type UnOp = rustc_middle::mir::UnOp;
#[derive(Debug, Clone)]
pub enum Lit {
    Int(u128, rustc_ast::ast::LitIntType),
    Bool(bool),
    Unsupported(String),
}
impl From<&rustc_ast::ast::LitKind> for Lit {
    fn from(lit: &rustc_ast::ast::LitKind) -> Self {
        match lit {
            &rustc_ast::ast::LitKind::Int(i, t) => Lit::Int(i, t),
            &rustc_ast::ast::LitKind::Bool(b) => Lit::Bool(b),
            other => Lit::Unsupported(format!("{other:?}")),
        }
    }
}
// pub type Lit = rustc_ast::ast::LitKind;

// 定义一个描述Suslik程序的结构体，它包括断言、函数签名等
pub struct SuslikProgram {
    pub(crate) pred_map: PredMap,
    pub(crate) extern_fns: Vec<Signature>,
    pub(crate) synth_fn: Signature,
    pub(crate) synth_ast: usize,
    pub(crate) pure_fn_ast: UsedPureFns,
}
// 函数签名
pub struct Signature {
    pub(crate) is_trivial: bool,
    pub(crate) region_rels: Vec<(String, String)>,
    pub(crate) pre: Assertion,
    pub(crate) post: Assertion,
    pub(crate) unique_name: String,
    pub(crate) fn_name: String,
}

// 谓词的结构体，包括标志、标识符、事实、子句等信息
pub struct Predicate {
    pub is_prim: bool,
    pub is_copy: bool,
    pub is_drop: bool,
    pub is_private: bool,
    pub ident: String, // used as key for Predicate map
    pub clean_name: String,
    // Fill in from fn_spec
    pub facts: Phi,
    pub fn_spec: Vec<PredParameter>,
    pub clauses: Vec<Clause>,
}

// 子句的结构体，包括名称、选择器、等式、断言等
pub struct Clause {
    pub name: Option<String>,
    pub prim_arg: Option<String>,
    pub selector: Expr,
    // Used as `Var(key) == value` for fns and futures
    pub equalities: FxHashMap<String, Expr>,
    pub assn: Assertion,
}

#[derive(Clone)]
pub struct SApp {
    pub is_private: bool,       // 是否为私有应用
    pub field_name: String,     // 字段名称
    pub ty: STy,                // 相关类型
}
#[derive(Clone)]
pub struct STy {
    // pub is_opaque: bool,
    pub is_brrw: Vec<BorrowInfo>, // 借用信息列表
    pub pred: String,             // 作为Predicate map的索引使用
    pub fn_spec: Vec<PredArgument>, // 函数参数列表
}
// 描述借用信息的结构体
#[derive(Clone, Debug)]
pub struct BorrowInfo {
    pub lft: String,              // 生命周期标识
    pub m: rustc_hir::Mutability, // 可变性
}


// 描述函数规范类型的枚举
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum FnSpecKind {
    Int,    // 整数类型
    Bool,   // 布尔类型
    Lft,    // 生命周期类型
    Set,    // 集合类型
    Snap,   // 快照类型
    // Tpl, 
}

impl FnSpecKind {
    // 将Rust类型转换为FnSpecKind
    pub fn prim_to_kind<'tcx>(ty: Ty<'tcx>) -> Self {
        match ty.kind() { //[匹配的类型种类]
            TyKind::Bool => Self::Bool,
            TyKind::Char => todo!(),
            TyKind::Int(_) | TyKind::Uint(_) => Self::Int,
            TyKind::Float(_) => todo!(),
            TyKind::Tuple(t) if t.is_empty() => Self::Int,
            TyKind::Adt(_, _) => match ty.to_string().as_str() {
                ty if ty.starts_with("russol_contracts::Set") => Self::Set,
                _ => todo!(),
            },
            _ => unreachable!(),
        }
    }
    pub fn is_snap(&self) -> bool {
        matches!(self, FnSpecKind::Snap)
    }
}

// 描述谓词参数的结构体
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct PredParameter {
    pub kind: FnSpecKind,   // 函数规范类型
    pub name: String,       // 参数名称
}
impl Default for PredParameter {
    fn default() -> Self {
        Self {
            kind: FnSpecKind::Snap,
            name: "snap".to_string(),
        }
    }
}
impl PredParameter {
    pub fn val(kind: FnSpecKind) -> Self {
        Self {
            kind,
            name: "snap".to_string(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PredArgument {
    pub name: String,
    pub target: PredParameter,
}

// 表达式的枚举类型
#[derive(Debug, Clone)]
pub enum Expr {
    // Never,
    Var(String),                      // 变量
    Snap(Vec<bool>, String),          // 快照类型
    OnExpiry(Vec<bool>, FnSpecKind, String, Result<usize, String>), // 到期操作
    Tuple(bool, Vec<Expr>),           // 元组类型
    Lit(Lit),                         // 文字
    BinOp(BinOp, Box<Expr>, Box<Expr>), // 二元操作
    UnOp(UnOp, Box<Expr>),            // 一元操作
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>), // If-Else表达式
}

// 描述一个断言的结构体，包括phi和sigma两个部分
pub struct Assertion {
    pub phi: Phi,
    pub sigma: Sigma,
}

impl Assertion {
    // 创建一个空的断言
    pub fn empty() -> Self {
        Self {
            phi: Phi::empty(),
            sigma: Sigma::empty(),
        }
    }
}
// 描述phi部分的结构体，包含一个表达式向量
#[derive(Debug, Clone)]
pub struct Phi(pub Vec<Expr>);

impl Phi {
    // 创建一个空的phi
    pub fn empty() -> Self {
        Self(Vec::new())
    }
}

// 描述sigma部分的结构体，包含一个SApp向量
pub struct Sigma(pub Vec<SApp>);
impl Sigma {
    // 创建一个空的sigma
    pub fn empty() -> Self {
        Self(Vec::new())
    }
}

// 描述一个不受支持的情况的结构体
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct Unsupported {
    pub in_main: bool, // 是否在主函数中
    pub reason: Reason, // 不受支持的原因
}

// 描述不受支持的原因的枚举
#[derive(serde::Serialize, serde::Deserialize, Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Reason {
    UnnamedArgs,
    LateBoundRegion,
    RequiresFlag,
    PrivateType,
    NonExhaustive,
    Other,
    CharFloat,
    ArraySlice,
    Closure,
    Unsafe,
    OtherTy,
}

// 描述合成结果的结构体
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct SynthesisResult {
    pub is_trivial: bool,              // 是否是一个简单结果
    pub kind: SynthesisResultKind,    // 合成结果的具体类型
}

// 描述合成结果类型的枚举
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub enum SynthesisResultKind {
    Unsupported(Unsupported),
    Unsolvable(u64),
    Timeout,
    Solved(Solved),
}

impl SynthesisResult {
    // 获取已解决的合成结果
    pub fn get_solved(&self) -> Option<&Solved> {
        if let SynthesisResultKind::Solved(sln) = &self.kind {
            Some(sln)
        } else {
            None
        }
    }

    // 获取不受支持的合成结果
    pub fn get_unsupported(&self) -> Option<&Unsupported> {
        if let SynthesisResultKind::Unsupported(u) = &self.kind {
            Some(u)
        } else {
            None
        }
    }

    // 获取不可解的合成结果
    pub fn get_unsolvable(&self) -> Option<u64> {
        if let SynthesisResultKind::Unsolvable(u) = &self.kind {
            Some(*u)
        } else {
            None
        }
    }

    // 判断是否为超时的合成结果
    pub fn is_timeout(&self) -> bool {
        matches!(self.kind, SynthesisResultKind::Timeout)
    }
}

// 定义一个使用纯函数的类型别名
pub type UsedPureFns = FxHashMap<String, (bool, usize)>;

// 描述一个已解决的合成结果的结构体
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct Solved {
    pub exec_time: u64,          // 执行时间
    pub synth_ast: usize,        // 合成抽象语法树的大小
    pub pure_fn_ast: UsedPureFns, // 使用的纯函数抽象语法树
    pub slns: Vec<Solution>,    // 解决方案向量
}

impl Solved {
    // 创建一个新的已解决的合成结果
    fn new(exec_time: u64, synth_ast: usize, pure_fn_ast: UsedPureFns, sln: String) -> Self {
        let idx = &mut 0;
        let slns: Vec<_> = sln
            .split("-----------------------------------------------------\n")
            .flat_map(|sln| Solution::new(sln, idx))
            .collect();
        Self {
            exec_time,
            synth_ast,
            pure_fn_ast,
            slns,
        }
    }

    // 打印已解决的合成结果
    pub fn print(&self) {
        let min_lines_print = std::env::var("RUSLIC_PRINT_SLN_ABOVE")
            .map(|v| v.parse::<usize>().unwrap())
            .unwrap_or(0);
        for sln in &self.slns {
            if sln.loc > min_lines_print {
                if self.slns.len() > 1 {
                    println!("[Solution #{}]", sln.idx);
                }
                print!("{}", sln.code);
            }
        }
    }
}
// 代表平均统计数据的结构体
// 代表平均统计数据的结构体
pub struct MeanStats {
    pub synth_time: f64,           // 合成时间
    pub loc: f64,                  // 代码行数
    pub spec_ast: f64,             // AST（抽象语法树）规格
    pub ast_nodes: f64,            // AST节点数量
    pub ast_nodes_unsimp: f64,     // 未简化的AST节点数量
    pub rule_apps: f64,            // 规则应用数量
}

impl MeanStats {
    // 创建新的MeanStats实例
    fn new() -> Self {
        Self {
            synth_time: 0.,
            loc: 0.,
            spec_ast: 0.,
            ast_nodes: 0.,
            ast_nodes_unsimp: 0.,
            rule_apps: 0.,
        }
    }

    // 从多个解决方案中计算统计数据
    pub fn calculate<'a>(many_slns: impl Iterator<Item = &'a Solved>) -> (UsedPureFns, Vec<Self>) {
        let mut count = Vec::new();
        let mut sums = Vec::new();
        let mut pure_fns = FxHashMap::default();

        // 遍历解决方案，并累计统计数据
        for solved in many_slns {
            for (k, &v) in &solved.pure_fn_ast {
                if let Some(&pfn) = pure_fns.get(k) {
                    assert_eq!(pfn, v, "key {k}");
                } else {
                    pure_fns.insert(k.clone(), v);
                }
            }
            for (idx, sln) in solved.slns.iter().enumerate() {
                if count.len() <= idx {
                    count.push(0.)
                }
                if sums.len() <= idx {
                    sums.push(Self::new())
                }
                count[idx] += 1.;
                sums[idx].synth_time += sln.synth_time as f64;
                sums[idx].loc += sln.loc as f64;
                sums[idx].spec_ast += solved.synth_ast as f64;
                sums[idx].ast_nodes += sln.ast_nodes as f64;
                sums[idx].ast_nodes_unsimp += sln.ast_nodes_unsimp as f64;
                sums[idx].rule_apps += sln.rule_apps as f64;
            }
        }

        // 计算均值
        for (sum, count) in sums.iter_mut().zip(count) {
            sum.synth_time /= count;
            sum.loc /= count;
            sum.spec_ast /= count;
            sum.ast_nodes /= count;
            sum.ast_nodes_unsimp /= count;
            sum.rule_apps /= count;
        }

        (pure_fns, sums)
    }
}

// 代表单个解决方案的结构体
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct Solution {
    pub code: String,          // 解决方案的代码
    pub loc: usize,            // 代码行数
    pub synth_time: u64,       // 合成时间
    pub ast_nodes: u64,        // AST节点数量
    pub ast_nodes_unsimp: u64, // 未简化的AST节点数量
    pub rule_apps: u64,        // 规则应用数量
    pub idx: usize,            // 解决方案的索引
}

impl Solution {
    // 根据代码和索引创建新的解决方案实例
    fn new(code: &str, idx: &mut usize) -> Option<Self> {
        let loc = code.lines().count();
        if loc <= 2 {
            return None;
        };
        let loc = loc - 2;
        assert!(code.starts_with("fn "), "{code}");
        let stats_str = code.split("@|").nth(1).unwrap();
        let mut stats_str = stats_str.split('|');
        let synth_time = stats_str.next().unwrap().parse().unwrap();
        let ast_nodes = stats_str.next().unwrap().parse().unwrap();
        let ast_nodes_unsimp = stats_str.next().unwrap().parse().unwrap();
        let rule_apps = stats_str.next().unwrap().parse().unwrap();
        *idx += 1;
        Some(Self {
            code: code.to_string(),
            loc,
            synth_time,
            ast_nodes,
            ast_nodes_unsimp,
            rule_apps,
            idx: *idx - 1,
        })
    }
}

impl SuslikProgram {
    /// 尝试解决给定的函数签名，可能会有超时限制。
    /// 超时时间以毫秒为单位
    pub fn solve<'tcx>(
        tcx: TyCtxt<'tcx>,
        sig: RuslikFnSig<'tcx>,
        pure_fns: &PureFnMap<'tcx>,
        extern_fns: &Vec<RuslikFnSig<'tcx>>,
        timeout: u64,
    ) -> Option<SynthesisResult> {
        // 构建或找到Suslik的路径
        let suslik_dir = Self::sbt_build_suslik();
        // 克隆函数参数
        let params = sig.params.clone();
        // 检查该函数签名是否是简单的（无法进一步分解的）
        let is_trivial = sig.is_trivial();

        // 尝试从给定的函数签名创建一个Suslik程序
        match Self::from_fn_sig(tcx, pure_fns, extern_fns, sig) {
            Ok(sp) => sp.send_to_suslik(suslik_dir, &params, timeout),  // 如果成功，发送给Suslik求解
            Err(err) => Some(SynthesisResult {   // 如果失败，返回一个表示不受支持的结果
                is_trivial,
                kind: SynthesisResultKind::Unsupported(err),
            }),
        }
    }

    /// 在一个新的线程中解决给定的函数签名
    pub fn solve_in_thread<'tcx>(
        tx: Sender<(usize, Option<SynthesisResult>)>,
        id: usize,
        tcx: TyCtxt<'tcx>,
        sig: RuslikFnSig<'tcx>,
        pure_fns: &PureFnMap<'tcx>,
        extern_fns: &Vec<RuslikFnSig<'tcx>>,
        timeout: u64,
    ) {
        // 构建或找到Suslik的路径
        let suslik_dir = Self::sbt_build_suslik();
        // 克隆函数参数
        let params = sig.params.clone();
        // 检查该函数签名是否是简单的
        let is_trivial = sig.is_trivial();
        let sus_prog = Self::from_fn_sig(tcx, pure_fns, extern_fns, sig);

        // 创建新线程
        std::thread::spawn(move || {
            // 根据前面的结果来尝试求解
            let result = match sus_prog {
                Ok(sp) => sp.send_to_suslik(suslik_dir, &params, timeout),
                Err(err) => Some(SynthesisResult {
                    is_trivial,
                    kind: SynthesisResultKind::Unsupported(err),
                }),
            };
            // 通过发送者发送结果
            tx.send((id, result)).unwrap();
        });
    }

    /// 找到或构建Suslik的路径
    fn sbt_build_suslik() -> PathBuf {
        // 首先尝试找到suslik的目录
        let suslik_dir = std::env::var("SUSLIK_DIR")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|_| {
                let mut suslik_dir = std::env::current_exe().unwrap();
                // 寻找存在的suslik目录
                while {
                    suslik_dir.push("suslik");
                    !suslik_dir.exists()
                } {
                    suslik_dir.pop();
                    if !suslik_dir.pop() {
                        break;
                    }
                }
                // 如果上述方法失败，尝试从当前目录查找suslik目录
                if suslik_dir.parent().is_none() {
                    suslik_dir = std::env::current_dir().unwrap();
                    while {
                        suslik_dir.push("suslik");
                        !suslik_dir.exists()
                    } {
                        suslik_dir.pop();
                        assert!(
                            suslik_dir.pop(),
                            "Failed to find suslik dir in parents of {}",
                            std::env::current_dir().unwrap().to_string_lossy()
                        );
                    }
                }
                suslik_dir
            });
        // 然后查找suslik的可执行文件
        let mut jar_file = suslik_dir.clone();
        jar_file.extend(["target", "scala-2.12", "suslik.jar"]);
        if !jar_file.is_file() {
            // 如果找不到，需要组装jar文件
            println!(
                "Running `sbt assembly` since there is no executable at {}",
                jar_file.to_string_lossy()
            );
            // 构建和运行sbt命令
            let mut assembly = Command::new(if cfg!(windows) { "cmd" } else { "sbt" });
            if cfg!(windows) {
                assembly.arg("/c").arg("sbt");
            }
            let mut assembly = assembly
                .arg("assembly")
                .current_dir(&suslik_dir)
                .spawn()
                .expect("`sbt assembly` command failed to start");
            assembly.wait().unwrap();
            assert!(
                jar_file.is_file(),
                "Running `sbt assembly` failed to create jar file at {}",
                jar_file.to_string_lossy()
            );
        }
        suslik_dir
    }


    fn send_to_suslik(
        &self,
        suslik_dir: PathBuf,
        params: &str,
        timeout: u64,
    ) -> Option<SynthesisResult> {
        // Write program to tmp file // 将程序写入临时文件
        let data = format!("# -c 10 -o 10 -p false\n###\n{}", self);
        let mut tmp = suslik_dir.clone();

        use rand::Rng; // 生成随机数作为临时目录名的一部分
        let num = rand::thread_rng().gen_range(0..10000);
        let tmpdir = std::path::PathBuf::from(format!("tmp-{}-{num}", self.synth_fn.unique_name));
        std::fs::create_dir_all(suslik_dir.join(&tmpdir)).unwrap();
        let synfile = tmpdir.join(std::path::PathBuf::from("tmp.syn"));
        tmp.push(&synfile);
        std::fs::write(tmp.clone(), data).expect("Unable to write file");
        // Run suslik on tmp file  // 在临时文件上运行suslik
        let mut provided_args = params
            .split(' ')
            .filter(|a| !a.is_empty())
            .map(String::from)
            .collect::<Vec<_>>();
        if provided_args.iter().all(|a| !a.contains("--solutions=")) { // 如果参数中没有包含 "--solutions="，则添加它
            provided_args.push("--solutions=1".to_string());
        }
        let output_trace = std::env::var("RUSLIC_OUTPUT_TRACE")
            .map(|v| v.parse::<bool>().unwrap())
            .unwrap_or(false);
        if output_trace {
            let logfile = tmpdir.join(std::path::PathBuf::from("trace.json"));
            let logfile = logfile.to_str();
            provided_args.push("-j".to_string());
            provided_args.push(logfile.unwrap().to_string());
        }
        let mut child = Command::new("java")
            .arg("-Dfile.encoding=UTF-8")
            .arg("-jar")
            .arg("./target/scala-2.12/suslik.jar")
            .arg(&synfile)
            .args(provided_args)
            .current_dir(&suslik_dir)
            .stdout(Stdio::piped())
            .spawn()
            .expect("`java` command failed to start");
        let mut stdout = child.stdout.take().unwrap();
        let start = Instant::now();
        let max = Duration::from_millis(timeout);
        let (intime, exit_status, time) = match child.wait_timeout(max).expect("sbt crashed?") {
            Some(status) => (true, status, start.elapsed()),
            None => {
                // child hasn't exited yet  // 子进程尚未退出
                child.kill().unwrap();
                println!("Failed to synthesize fn after {}ms!", timeout);
                (false, child.wait().unwrap(), max)
            }
        };
        let fail_on_unsynth = std::env::var("RUSLIC_FAIL_ON_UNSYNTH")
            .map(|v| v.parse::<bool>().unwrap())
            .unwrap_or(true);
        let unsolvable = exit_status.code().unwrap_or(0) == 2;
        let failed = !exit_status.success() && (fail_on_unsynth || !unsolvable);
        if intime && failed {
            println!(
                "suslik failed ({}) for {}",
                exit_status, self.synth_fn.fn_name
            );
            None
        } else { // 解析 suslik 的输出结果并返回相应的结构体
            Some(if !intime {
                SynthesisResult {
                    is_trivial: self.synth_fn.is_trivial,
                    kind: SynthesisResultKind::Timeout,
                }
            } else if unsolvable {
                std::fs::remove_dir_all(suslik_dir.join(&tmpdir)).unwrap();
                SynthesisResult {
                    is_trivial: self.synth_fn.is_trivial,
                    kind: SynthesisResultKind::Unsolvable(time.as_millis() as u64),
                }
            } else {
                std::fs::remove_dir_all(suslik_dir.join(&tmpdir)).unwrap();
                let mut sln = String::new();
                use std::io::Read;
                stdout.read_to_string(&mut sln).unwrap();
                SynthesisResult {
                    is_trivial: self.synth_fn.is_trivial,
                    kind: SynthesisResultKind::Solved(Solved::new(
                        time.as_millis() as u64,
                        self.synth_ast,
                        self.pure_fn_ast.clone(),
                        sln,
                    )),
                }
            })
        }
    }

    // 从给定的函数签名创建新的实例
    fn from_fn_sig<'a, 'tcx>(
        tcx: TyCtxt<'tcx>, // 类型上下文
        pure_fns: &'a PureFnMap<'tcx>, // 纯函数的映射
        extern_fns: &Vec<RuslikFnSig<'tcx>>, // 外部函数的列表
        sig: RuslikFnSig<'tcx>, // 当前的函数签名
    ) -> Result<Self, Unsupported> {

        // 从给定的函数签名提取 def_id 和 ast_nodes
        let def_id = sig.def_id;
        let ast_nodes = sig.ast_nodes;

        // 创建一个默认的 FxHashMap
        let mut map = FxHashMap::default();

        // 从给定的函数签名、纯函数映射和 map 中提取签名
        let ssig = Signature::from_fn_sig(tcx, pure_fns, sig, &mut map)?;

        // 查找与 def_id 和 ssig.tys 相关的 trait 函数
        let trait_fns = find_trait_fns(tcx, def_id, &ssig.tys);

        // 对于每个 trait 函数，尝试从函数签名映射中提取签名，并收集所有有效的签名
        let mut efns = trait_fns
            .into_iter()
            .flat_map(|tf| {
                Signature::from_fn_sig_map(tcx, pure_fns, tf, &mut map, false)
                    .map(|sig| sig.sig)
                    .ok()
            })
            .collect::<Vec<Signature>>();

        // 创建一个泛型收集器实例
        let sgc = SGenericsCollector {
            tcx,
            synth_tys: ssig.tys,
        };

        // 对于每个外部函数，找到所有子函数并为其创建新的签名
        for efn in extern_fns {
            for (gens, efn) in sgc.find_subs_for_ext_fns(efn) {
                let mut sig = Signature::from_fn_sig_map(tcx, pure_fns, efn, &mut map, false)?;
                sig.sig.unique_name = sig.sig.unique_name + "_" + &gens; // 修改 unique_name
                efns.push(sig.sig); // 将新签名添加到 efns 列表中
            }
        }

        // 使用收集的数据创建结果实例
        let mut res = Self {
            pred_map: map,
            extern_fns: efns,
            synth_fn: ssig.sig,
            synth_ast: ast_nodes,
            pure_fn_ast: ssig
                .used_pure_fns
                .into_iter()
                .map(|pfn| {
                    (
                        tcx.def_path_str(pfn.def_id),
                        (pfn.executable, pfn.ast_nodes),
                    )
                })
                .collect(),
        };
        
        res.normalize(); // 规范化结果实例
        Ok(res) // 返回成功创建的实例
    }
}


// 定义一个结构 SignatureSuccess，它包含三个字段。
pub struct SignatureSuccess<'a, 'tcx> {
    sig: Signature,                               // 一个Signature类型的字段。
    tys: FxHashSet<rustc_middle::ty::Ty<'tcx>>,   // 使用FxHashSet存储类型集合。
    used_pure_fns: Vec<&'a PureFn<'tcx>>,         // 存储被使用的纯函数的集合。
}

// 对结构Signature的实现。
impl Signature {
     // 定义一个公共函数 from_fn_sig。
    pub fn from_fn_sig<'a, 'tcx>(
        tcx: TyCtxt<'tcx>,
        pure_fns: &'a PureFnMap<'tcx>,
        sig: RuslikFnSig<'tcx>,
        map: &mut PredMap,
    ) -> Result<SignatureSuccess<'a, 'tcx>, Unsupported> {
        Self::from_fn_sig_map(tcx, pure_fns, sig, map, true)
    }
    // 定义一个公共函数 from_fn_sig_map。
    pub fn from_fn_sig_map<'a, 'tcx>(
        tcx: TyCtxt<'tcx>,
        pure_fns: &'a PureFnMap<'tcx>,
        sig: RuslikFnSig<'tcx>,
        map: &mut PredMap,
        in_main: bool,
    ) -> Result<SignatureSuccess<'a, 'tcx>, Unsupported> {
         // 检查环境变量 "RUSLIC_USE_FULL_NAMES" 的值
        let use_full_names = std::env::var("RUSLIC_USE_FULL_NAMES")
            .map(|v| v.parse::<bool>().unwrap())
            .unwrap_or(false);
        // 检查环境变量 "RUSLIC_OPTIMISTICALLY_ALLOW_PRIVATE_TYPES" 的值。
        let optimistically_allow_private_types =
            std::env::var("RUSLIC_OPTIMISTICALLY_ALLOW_PRIVATE_TYPES")
                .map(|v| v.parse::<bool>().unwrap())
                .unwrap_or(false);
        // 初始化一个 STyTranslator 结构的实例。
        let mut stt = STyTranslator {
            use_full_names,
            optimistically_allow_private_types,
            tcx,
            map,
            tys: FxHashSet::default(),
            fn_id: sig.def_id,
        };
         // 检查函数的参数中是否有任何没有 UUID 的参数
        if sig.args.iter().any(|(v, _)| v.uuid().is_empty()) {
            // 如果有，则返回一个错误：不支持这样的函数。
            // functions with args (_: i32, Struct { f }: Struct) not supported
            return Err(Unsupported {
                in_main,
                reason: Reason::UnnamedArgs,
            });
        }
        // 对函数的每个参数进行转换。
        let sigma = Sigma(
            sig.args
                .iter()
                .enumerate()
                .map(|(_card, (v, ty))|
            // The leading `f` is cut off in suslik:
            stt.translate_sapp(false, &v.rname(), *ty))
                .collect::<Result<_, _>>()
                .map_err(|reason| Unsupported { in_main, reason })?,
        );
        // 初始化一个 Assertion 结构的实例。
        let mut pre = Assertion {
            phi: Phi::empty(),
            sigma,
        };
        let mut used_pure_fns = Vec::new();
          // 初始化一个 ExprTranslator 结构的实例。
        let mut et = ExprTranslator {
            tcx,
            pre: &mut pre,
            post: &mut Assertion::empty(),
            pure_fns,
            map: stt.map,
            call_params: None,
            is_fn_body: false,
            under_cond: Vec::new(),
            used_pure_fns: &mut used_pure_fns,
        };
        // 将 pure_pre 表达式转换为其等效的 Phi 表达式。
        let expr = et.translate_expr(&sig.pure_pre, Vec::new(), None);
        pre.phi.0.extend(expr.flatten());

        // TODO: remove special treatment of unit
        let result = if !sig.ret.is_unit() {
            Some(
                stt.translate_sapp(false, "result", sig.ret)
                    .map_err(|reason| Unsupported { in_main, reason })?,
            )
        } else {
            None
        };
        let sigma = if let Some(result) = result {
            Sigma(vec![result])
        } else {
            Sigma::empty()
        };
        // let result = stt.translate_sapp(false, "result", sig.ret)
        //             .map_err(|reason| Unsupported { in_main, reason })?;
        // let sigma = Sigma(vec![result]);
        let mut post = Assertion {
            phi: Phi::empty(),
            sigma,
        };
        let mut et = ExprTranslator {
            tcx,
            pre: &mut pre,
            post: &mut post,
            pure_fns,
            map: stt.map,
            call_params: None,
            is_fn_body: false,
            under_cond: Vec::new(),
            used_pure_fns: &mut used_pure_fns,
        };

        // let lfts = et.translate_lfts();

        let expr = et.translate_expr(&sig.pure_post, Vec::new(), None);
        post.phi.0.extend(expr.flatten());

        // pre.phi.0.extend(lfts.flatten());
        let mut fn_name = tcx.item_name(sig.def_id).to_string();
        if !in_main
            && sig
                .args
                .first()
                .map(|arg| arg.0.uuid() != "self")
                .unwrap_or(true)
        {
            use crate::rustc_middle::ty::DefIdTree;
            if let Some(parent) = tcx.opt_parent(sig.def_id) && tcx.def_kind(parent) == DefKind::Trait {
                // let trait_name = tcx.item_name(parent);
                let trait_name = tcx.def_path_str(parent);
                let prefix = if trait_name.contains("::") && parent.is_local() { "crate::".to_string() } else { String::new() };
                fn_name = prefix + trait_name.split('<').next().unwrap() + "::" + &fn_name;
            }
        }
        let sig = Self {
            is_trivial: sig.is_trivial(),
            region_rels: outlives_relations(tcx, &sig),
            pre,
            post,
            unique_name: crate::suslik_translate::sanitize(&tcx.def_path_str(sig.def_id)),
            fn_name,
        };
         // 根据上面的计算和转换，构建并返回一个 SignatureSuccess 实例
        Ok(SignatureSuccess {
            sig,
            tys: stt.tys,
            used_pure_fns,
        })
    }
}

impl Expr {
     // 将表达式展平为一个 Vec<Self>（向量）。主要处理`And`二元操作。
    pub fn flatten(self) -> Vec<Self> {
        match self {
             // 如果表达式是二元操作且操作是`And`
            Expr::BinOp(BinOp::Rust(RustBinOp::And), l, r) => {
                 // 展平左子表达式
                let mut l = l.flatten();
                // 将右子表达式的展平结果追加到左子表达式的展平结果后
                l.extend(r.flatten());
                l
            }
             // 其他类型的表达式直接放入向量中
            other => vec![other],
        }
    }
     // 更新表达式中的变量名。接受一个函数`f`作为参数，该函数对变量名执行某些操作。
    pub fn update_vars<F: Fn(&mut String)>(&mut self, f: &F) {
        match self {
            // 对于这些类型的表达式，应用函数`f`来更新变量`v`
            Expr::Var(v) | Expr::Snap(_, v) | Expr::OnExpiry(_, _, v, _) => f(v),
            // 对于元组表达式，递归更新每一个子表达式
            Expr::Tuple(_, es) => {
                for e in es {
                    e.update_vars(f)
                }
            }
            // 对于字面量表达式，什么也不做
            Expr::Lit(_) => (),
             // 对于二元操作，递归更新左右子表达式
            Expr::BinOp(_, l, r) => {
                l.update_vars(f);
                r.update_vars(f);
            }
            Expr::UnOp(_, e) => e.update_vars(f),
            // 对于条件表达式，递归更新条件、真值子表达式和假值子表达式
            Expr::IfElse(b, t, e) => {
                b.update_vars(f);
                t.update_vars(f);
                e.update_vars(f);
            }
        }
    }
     // 如果表达式中的变量名为 "fresult"，则使用 `e_new` 替换该表达式
    pub fn update_result(&mut self, e_new: &Self) {
        match self {
            Expr::Var(v) | Expr::Snap(_, v) | Expr::OnExpiry(_, _, v, _) => {
                if v == "fresult" {
                    *self = e_new.clone();
                }
            }
            Expr::Tuple(_, es) => {
                for e in es {
                    e.update_result(e_new)
                }
            }
            Expr::Lit(_) => (),
            Expr::BinOp(_, l, r) => {
                l.update_result(e_new);
                r.update_result(e_new);
            }
            Expr::UnOp(_, e) => e.update_result(e_new),
            Expr::IfElse(b, t, e) => {
                b.update_result(e_new);
                t.update_result(e_new);
                e.update_result(e_new);
            }
        }
    }
    // 更改变量名。该函数接受一个函数`f`作为参数，该函数根据当前变量名可能返回一个新的表达式。
    pub fn change_var<F: Fn(&str) -> Option<Expr>>(&mut self, f: &F) {
        match self {
            // 对于变量表达式，应用函数`f`，如果返回了新的表达式，则用新表达式替换当前表达式
            Expr::Var(v) => {
                if let Some(new) = f(v) {
                    *self = new;
                }
            }
            Expr::Snap(_, _) => (),
            Expr::OnExpiry(_, _, _, _) => (),
            Expr::Tuple(_, es) => {
                for e in es {
                    e.change_var(f)
                }
            }
            Expr::Lit(_) => (),
            Expr::BinOp(_, l, r) => {
                l.change_var(f);
                r.change_var(f);
            }
            Expr::UnOp(_, e) => e.change_var(f),
            Expr::IfElse(b, t, e) => {
                b.change_var(f);
                t.change_var(f);
                e.change_var(f);
            }
        }
    }
    pub fn prim_to_invs<'tcx>(value: String, kind: &'tcx TyKind<'tcx>) -> Phi {
        match *kind {
            TyKind::Bool => Phi::empty(),
            TyKind::Char => todo!(),
            TyKind::Int(i) => {
                let i = if matches!(i, rustc_middle::ty::IntTy::Isize) {
                    rustc_middle::ty::IntTy::I64
                } else {
                    i
                };
                // TODO: Scala Ints cannot parse such big values
                let (subtract, i) = match i {
                    IntTy::I8 => (0, IntTy::I8),
                    IntTy::I16 => (0, IntTy::I16),
                    IntTy::I32 => (2, IntTy::I32),
                    IntTy::I64 => (1, IntTy::I32),
                    IntTy::I128 => (0, IntTy::I32),
                    IntTy::Isize => unreachable!(),
                };
                let max_val = (1 << (i.bit_width().unwrap() - 1)) - 1 - subtract;
                Phi(vec![
                    Expr::BinOp(
                        RustBinOp::Ge.into(),
                        Box::new(Expr::Var(value.clone())),
                        Box::new(Expr::UnOp(UnOp::Neg, Box::new(max_val.into()))),
                    ),
                    Expr::BinOp(
                        RustBinOp::Le.into(),
                        Box::new(Expr::Var(value)),
                        Box::new(max_val.into()),
                    ),
                ])
            }
            TyKind::Uint(u) => {
                let u = if matches!(u, rustc_middle::ty::UintTy::Usize) {
                    rustc_middle::ty::UintTy::U64
                } else {
                    u
                };
                // TODO: Scala Ints cannot parse such big values
                let (subtract, u) = match u {
                    UintTy::U8 => (u128::MAX, UintTy::U8),
                    UintTy::U16 => (u128::MAX, UintTy::U16),
                    UintTy::U32 => (0, UintTy::U16),
                    UintTy::U64 => (1, UintTy::U16),
                    UintTy::U128 => (2, UintTy::U16),
                    UintTy::Usize => unreachable!(),
                };
                let max_val = (u128::checked_shl(1, u.bit_width().unwrap() as u32))
                    .unwrap_or(0)
                    .wrapping_add(subtract)
                    .into();
                Phi(vec![
                    Expr::BinOp(
                        RustBinOp::Ge.into(),
                        Box::new(Expr::Var(value.clone())),
                        Box::new(0.into()),
                    ),
                    Expr::BinOp(RustBinOp::Le.into(), Box::new(Expr::Var(value)), Box::new(max_val)),
                ])
            }
            TyKind::Float(_) => todo!(),
            TyKind::Tuple(t) if t.is_empty() => Phi::empty(),
            _ => unreachable!(),
        }
    }
    pub fn _eq(self, other: Self) -> Self {
        Self::BinOp(RustBinOp::Eq.into(), Box::new(self), Box::new(other))
    }
    pub fn is_true(&self) -> bool {
        matches!(self, Expr::Lit(Lit::Bool(true)))
    }
}
impl From<u128> for Expr {
    fn from(u: u128) -> Self {
        Expr::Lit(Lit::Int(u, LitIntType::Unsuffixed))
    }
}
impl From<bool> for Expr {
    fn from(b: bool) -> Self {
        Expr::Lit(Lit::Bool(b))
    }
}
impl std::ops::BitAnd<Expr> for Expr {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        match (&self, &rhs) {
            // Optimizations:
            (Expr::Lit(Lit::Bool(true)), _) | (_, Expr::Lit(Lit::Bool(false))) => rhs,
            (_, Expr::Lit(Lit::Bool(true))) | (Expr::Lit(Lit::Bool(false)), _) => self,
            // Constructor:
            _ => Expr::BinOp(RustBinOp::And.into(), Box::new(self), Box::new(rhs)),
        }
    }
}
