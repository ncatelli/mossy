use crate::ast::*;

pub fn interpret(node: ExprNode) -> IntegerConstant {
    match node {
        ExprNode::Primary(num) => num,
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
) -> IntegerConstant {
    let lhs = interpret(lhs);
    let rhs = interpret(rhs);

    match (op, lhs, rhs) {
        (BinaryOperator::Plus, IntegerConstant(l), IntegerConstant(r)) => IntegerConstant(l + r),
        (BinaryOperator::Minus, IntegerConstant(l), IntegerConstant(r)) => IntegerConstant(l - r),
        (BinaryOperator::Star, IntegerConstant(l), IntegerConstant(r)) => IntegerConstant(l * r),
        (BinaryOperator::Slash, IntegerConstant(l), IntegerConstant(r)) => IntegerConstant(l / r),
    }
}
