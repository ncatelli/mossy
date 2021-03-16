use crate::ast;

impl std::ops::Add for ast::Literal {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let Self::Int(left) = self;
        let Self::Int(right) = rhs;

        Self::Output::Int(left + right)
    }
}

impl std::ops::Sub for ast::Literal {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let Self::Int(left) = self;
        let Self::Int(right) = rhs;

        Self::Output::Int(left - right)
    }
}

impl std::ops::Mul for ast::Literal {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let Self::Int(left) = self;
        let Self::Int(right) = rhs;

        Self::Output::Int(left * right)
    }
}

impl std::ops::Div for ast::Literal {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let Self::Int(left) = self;
        let Self::Int(right) = rhs;

        Self::Output::Int(left / right)
    }
}

pub fn interpret(node: ast::Expr) -> ast::Literal {
    use ast::{AdditionExpr, DivisionExpr, Expr, MultiplicationExpr, SubtractionExpr};
    match node {
        Expr::Primary(lit) => lit,
        Expr::Addition(AdditionExpr(left, right)) => interpret(*left) + interpret(*right),
        Expr::Subtraction(SubtractionExpr(left, right)) => interpret(*left) - interpret(*right),

        Expr::Multiplication(MultiplicationExpr(left, right)) => {
            interpret(*left) * interpret(*right)
        }
        Expr::Division(DivisionExpr(left, right)) => interpret(*left) / interpret(*right),
    }
}
