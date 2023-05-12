use lr_core::prelude::v1::*;
use lr_core::TerminalOrNonTerminal;
pub use lr_derive::Lr1;

mod lexer;
use lexer::{Token, TokenKind};

#[derive(Debug, PartialEq)]
pub struct UnaryExpr<'a> {
    pub lhs: NonTerminal<'a>,
}

impl<'a> UnaryExpr<'a> {
    pub fn new(lhs: NonTerminal<'a>) -> Self {
        Self { lhs }
    }
}

#[derive(Debug, PartialEq)]
pub enum ExprInner<'a> {
    Unary(UnaryExpr<'a>),
}

type TermOrNonTerm<'a> = TerminalOrNonTerminal<Token<'a>, NonTerminal<'a>>;

#[allow(unused)]
fn reduce_unary_expression<'a>(
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    // the only top level expr is an additive expr.
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Constant(inner))) = elems.pop() {
        let inner = ExprInner::Unary(UnaryExpr::new(NonTerminal::Constant(inner)));

        Ok(NonTerminal::<'a>::Expression(Box::new(inner)))
    } else {
        Err("expected non-terminal at top of stack".to_string())
    }
}

/// Caller assumes
#[allow(unused)]
fn reduce_constant<'a>(elems: &mut Vec<TermOrNonTerm<'a>>) -> Result<NonTerminal<'a>, String> {
    match elems.pop() {
        Some(TermOrNonTerm::Terminal(
            term @ Token {
                kind: TokenKind::IntegerConstant,
                ..
            },
        ))
        | Some(TermOrNonTerm::Terminal(
            term @ Token {
                kind: TokenKind::CharacterConstant,
                ..
            },
        ))
        | Some(TermOrNonTerm::Terminal(
            term @ Token {
                kind: TokenKind::FloatingConstant,
                ..
            },
        )) => Ok(NonTerminal::Constant(term)),

        _ => Err("expected constant terminal at top of stack".to_string()),
    }
}

#[derive(Debug, Lr1, PartialEq)]
pub enum NonTerminal<'a> {
    #[goal(r"<Expression>", reduce_unary_expression)]
    #[production(r"<Constant>", reduce_unary_expression)]
    Expression(Box<ExprInner<'a>>),
    #[production(r"Token::IntegerConstant", reduce_constant)]
    #[production(r"Token::CharacterConstant", reduce_constant)]
    #[production(r"Token::FloatingConstant", reduce_constant)]
    Constant(Token<'a>),
}

impl<'a> NonTerminalRepresentable for NonTerminal<'a> {
    type Terminal = Token<'a>;
}

pub fn parse<'a>(input: &'a str) -> Result<NonTerminal<'a>, String> {
    let eof_terminator_token = {
        let eof_terminator = Token::eof();
        let end_idx = input.len();
        let end_cursor = lexer::Cursor::new(end_idx, 0, 0);
        let end_span = lexer::Span::new(end_cursor, end_cursor);

        Token::new(end_span, eof_terminator)
    };

    let tokenizer = lexer::Scanner::new(input)
        .into_iter()
        // This appends an eof token to the end of the scanned stream for use within the above production.
        .chain([Ok(eof_terminator_token)].into_iter())
        .flatten();

    LrParseable::parse_input(tokenizer)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_parse_standalone_constants() {
        let inputs = [
            "5",   // integer constant
            "'c'", // character constant
            "5.0", // floating constant
        ];

        for input in inputs {
            let maybe_parse_tree = parse(&input);

            assert!(maybe_parse_tree.is_ok());
        }
    }
}
