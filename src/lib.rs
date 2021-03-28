pub mod ast;
pub mod parser;

#[cfg(test)]
mod tests {
    #[test]
    fn should_interpret_arithmetic_input() {
        let input: Vec<char> = "2 + 3 * 5 - 8 / 3".chars().collect();

        assert_eq!(
            Ok(crate::ast::IntegerConstant(15)),
            crate::parser::parse(&input).map(crate::ast::interpret::interpret)
        )
    }

    #[test]
    fn should_interpret_arithmetic_input_with_arbitrary_whitespace() {
        let input: Vec<char> = "13 -6+  4*
        5
               +
        08 / 3"
            .chars()
            .collect();
        assert_eq!(
            Ok(crate::ast::IntegerConstant(29)),
            crate::parser::parse(&input).map(crate::ast::interpret::interpret)
        )
    }
}
