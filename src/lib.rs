pub mod ast;
pub mod codegen;
pub mod parser;

#[cfg(test)]
mod tests {
    use crate::ast;

    #[test]
    fn should_interpret_arithmetic_input() {
        let input: Vec<(usize, char)> = "2 + 3 * 5 - 8 / 3;".chars().enumerate().collect();

        assert_eq!(
            Ok(Some(crate::ast::Uint8(15))),
            crate::parser::parse(&input).map(|stmts| match stmts.get(0) {
                Some(ast::StmtNode::Expression(expr)) => {
                    Some(crate::ast::interpret::interpret(expr.to_owned()))
                }
                _ => None,
            })
        )
    }

    #[test]
    fn should_interpret_arithmetic_input_with_arbitrary_whitespace() {
        let input: Vec<(usize, char)> = "13 -6+  4*
        5
               +
        08 / 3;"
            .chars()
            .enumerate()
            .collect();

        assert_eq!(
            Ok(Some(crate::ast::Uint8(29))),
            crate::parser::parse(&input).map(|stmts| match stmts.get(0) {
                Some(ast::StmtNode::Expression(expr)) => {
                    Some(crate::ast::interpret::interpret(expr.to_owned()))
                }
                _ => None,
            })
        )
    }
}
