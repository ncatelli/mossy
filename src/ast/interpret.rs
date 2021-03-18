use crate::ast::*;

pub fn interpret(node: AstNode) -> Number {
    match node {
        AstNode::Expression(be) => interpret_binary_expression(be),
        AstNode::Number(num) => num,
    }
}

pub fn interpret_binary_expression(be: BinaryExpr) -> Number {
    let (tok, alhs, arhs) = match be {
        BinaryExpr::Plus(lhs, rhs) => ('+', *lhs, *rhs),
        BinaryExpr::Minus(lhs, rhs) => ('-', *lhs, *rhs),
        BinaryExpr::Multiply(lhs, rhs) => ('*', *lhs, *rhs),
        BinaryExpr::Divide(lhs, rhs) => ('/', *lhs, *rhs),
    };

    let lhs = interpret(alhs);
    let rhs = interpret(arhs);

    match (tok, lhs, rhs) {
        ('+', Number(l), Number(r)) => Number(l + r),
        ('-', Number(l), Number(r)) => Number(l - r),
        ('*', Number(l), Number(r)) => Number(l * r),
        ('/', Number(l), Number(r)) => Number(l / r),
        _ => panic!("this will never be hit"),
    }
}
