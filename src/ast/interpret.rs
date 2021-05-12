use crate::ast::*;

pub fn interpret(node: ExprNode) -> Uint8 {
    match node {
        ExprNode::Primary(Primary::Uint8(num)) => num,
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
) -> Uint8 {
    let lhs = interpret(lhs);
    let rhs = interpret(rhs);

    match (op, lhs, rhs) {
        (BinaryOperator::Plus, Uint8(l), Uint8(r)) => Uint8(l + r),
        (BinaryOperator::Minus, Uint8(l), Uint8(r)) => Uint8(l - r),
        (BinaryOperator::Star, Uint8(l), Uint8(r)) => Uint8(l * r),
        (BinaryOperator::Slash, Uint8(l), Uint8(r)) => Uint8(l / r),
    }
}

#[cfg(test)]
mod tests {

    use crate::ast::*;

    #[test]
    fn should_interpret_primary_ast_result() {
        let ast = ExprNode::Primary(Primary::Uint8(Uint8(5)));

        assert_eq!(Uint8(5), crate::ast::interpret::interpret(ast))
    }

    #[test]
    fn should_interpret_expected_arithmetic_result() {
        // 5 + 5
        let ast = ExprNode::Addition(
            Box::new(ExprNode::Primary(Primary::Uint8(Uint8(5)))),
            Box::new(ExprNode::Primary(Primary::Uint8(Uint8(5)))),
        );

        // 5 + 5 == 10
        assert_eq!(Uint8(10), crate::ast::interpret::interpret(ast))
    }
}
