use crate::ast::*;

pub fn interpret(node: ExprNode) -> Number {
    match node {
        ExprNode::Number(num) => num,
        ExprNode::Addition(lhs, rhs) => {
            interpret_binary_arithmetic_expression(BinaryOperator::Plus, *lhs, *rhs)
        }
        ExprNode::Subtraction(lhs, rhs) => {
            interpret_binary_arithmetic_expression(BinaryOperator::Minus, *lhs, *rhs)
        }
        ExprNode::Multiplication(lhs, rhs) => {
            interpret_binary_arithmetic_expression(BinaryOperator::Star, *lhs, *rhs)
        }
        ExprNode::Division(lhs, rhs) => {
            interpret_binary_arithmetic_expression(BinaryOperator::Slash, *lhs, *rhs)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum BinaryOperator {
    Plus,
    Minus,
    Star,
    Slash,
}

fn interpret_binary_arithmetic_expression(
    op: BinaryOperator,
    lhs: ExprNode,
    rhs: ExprNode,
) -> Number {
    let lhs = interpret(lhs);
    let rhs = interpret(rhs);

    match (op, lhs, rhs) {
        (BinaryOperator::Plus, Number(l), Number(r)) => Number(l + r),
        (BinaryOperator::Minus, Number(l), Number(r)) => Number(l - r),
        (BinaryOperator::Star, Number(l), Number(r)) => Number(l * r),
        (BinaryOperator::Slash, Number(l), Number(r)) => Number(l / r),
    }
}
