use rustc_middle::ty::{TypeFoldable, TypeFolder};

use crate::ruslik_pure::{CallInfo, ExprKind, PureExpression};

// 对 `PureExpression` 类型进行实现
impl<'tcx> PureExpression<'tcx> {
    pub fn walk_mut<T: PureExpressionWalker<'tcx>>(&mut self, walker: &mut T) {
        walker.walk_kind_mut(self.kind_mut());
    }
}
// 对 `ExprKind` 类型进行实现
impl<'tcx> ExprKind<'tcx> {
    pub fn walk_mut<T: PureExpressionWalker<'tcx>>(&mut self, walker: &mut T) {
        match self {
            ExprKind::Never | ExprKind::Var(_) | ExprKind::Lit(_) => (),
            ExprKind::BinOp(_, l, r) => {
                walker.walk_expr_mut(l);
                walker.walk_expr_mut(r);
            }
            ExprKind::UnOp(_, e) | ExprKind::Field(e, _, _) => walker.walk_expr_mut(e),
            ExprKind::Constructor(_, _, es) => {
                for e in es {
                    walker.walk_expr_mut(&mut e.1)
                }
            }
            ExprKind::IfElse(c, t, e) => {
                walker.walk_expr_mut(c);
                walker.walk_expr_mut(t);
                walker.walk_expr_mut(e);
            }
            ExprKind::Call(_, es) => {
                for e in es {
                    walker.walk_expr_mut(e)
                }
            }
        }
    }
}


// 定义了一个名为 PureExpressionWalker 的 trait。
// 该 trait 的生命周期为 'tcx，并且它仅适用于满足 Sized trait 的类型。
pub trait PureExpressionWalker<'tcx>: Sized {

    // 该方法接收一个类型为 PureExpression 的可变引用 e，
    // 并在 e 上调用 walk_mut 方法来递归遍历并可能修改 e 的结构。
    fn walk_expr_mut(&mut self, e: &mut PureExpression<'tcx>) {
        e.walk_mut(self);
    }

    // 该方法接收一个类型为 ExprKind 的可变引用 k，
    // 并根据 k 的不同形态，进行相应的递归遍历和潜在修改。
    fn walk_kind_mut(&mut self, k: &mut ExprKind<'tcx>) {
        // ... [此处省略了 match 内容以便于阅读]
    }
}

// 下面是针对满足 TypeFolder trait 的类型的 PureExpressionWalker trait 的默认实现：
impl<'tcx, F: TypeFolder<'tcx>> PureExpressionWalker<'tcx> for F {

    // 该方法首先将 e 的类型通过 fold_ty 方法进行转换，
    // 然后在 e 上调用 walk_mut 方法来递归遍历并可能修改 e 的结构。
    fn walk_expr_mut(&mut self, e: &mut PureExpression<'tcx>) {
        *e.ty_mut() = self.fold_ty(e.ty());
        e.walk_mut(self);
    }

    // 该方法根据 k 的具体形态进行相应的递归遍历和潜在修改。
    // 特别的，对于形态为 Call(CallInfo::Pure(_, gas), _) 的 k，
    // 会调用 fold_with 方法进行转换。
    fn walk_kind_mut(&mut self, k: &mut ExprKind<'tcx>) {
        if let ExprKind::Call(CallInfo::Pure(_, gas), _) = k {
            *gas = gas.fold_with(self);
        }
        k.walk_mut(self);
    }
}
