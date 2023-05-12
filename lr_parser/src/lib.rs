use lr_core::prelude::v1::*;
use lr_core::TerminalOrNonTerminal;
pub use lr_derive::Lr1;

mod lexer;
use lexer::{Token, TokenKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeRef<'a> {
    _lifetime: std::marker::PhantomData<&'a ()>,
    idx: usize,
}

impl<'a> NodeRef<'a> {
    pub fn new(idx: usize) -> Self {
        Self {
            _lifetime: std::marker::PhantomData,
            idx,
        }
    }

    pub fn as_usize(&self) -> usize {
        self.idx
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnaryExpr<'a> {
    pub lhs: NodeRef<'a>,
}

impl<'a> UnaryExpr<'a> {
    pub fn new(lhs: NodeRef<'a>) -> Self {
        Self { lhs }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprInner<'a> {
    Unary(UnaryExpr<'a>),
}

type TermOrNonTerm<'a> = TerminalOrNonTerminal<Token<'a>, NonTerminal<'a>>;

/// Caller assumes
#[allow(unused)]
fn reduce_constant<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
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
        )) => {
            let node = ParseTreeNode::Constant(term);
            let nt_ref = state.add_node_mut(node);

            Ok(NonTerminal::Constant(nt_ref))
        }

        _ => Err("expected constant terminal at top of stack".to_string()),
    }
}

#[allow(unused)]
fn reduce_unary_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    // the only top level expr is an additive expr.
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Constant(inner))) = elems.pop() {
        let inner = ExprInner::Unary(UnaryExpr::new(inner));
        let node = ParseTreeNode::Expression(inner);
        let nt_ref = state.add_node_mut(node);

        Ok(NonTerminal::Expression(nt_ref))
    } else {
        Err("expected non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_goal<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    // the only top level expr is an additive expr.
    if let Some(TermOrNonTerm::NonTerminal(inner)) = elems.pop() {
        Ok(inner)
    } else {
        Err("expected non-terminal at top of stack".to_string())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParseCtx<'a> {
    _lifetime: std::marker::PhantomData<&'a ()>,
    arena: Vec<ParseTreeNode<'a>>,
}

impl<'a> ParseCtx<'a> {
    const DEFAULT_CAPACITY: usize = 64;
}

impl<'a> ParseCtx<'a> {
    pub fn nodes(&self) -> usize {
        self.arena.len()
    }

    fn next_nonterminal_ref(&self) -> NodeRef<'a> {
        let idx = self.arena.len();

        NodeRef::new(idx)
    }

    fn add_node_mut(&mut self, node: ParseTreeNode<'a>) -> NodeRef<'a> {
        let nt_ref = self.next_nonterminal_ref();
        self.arena.push(node);

        nt_ref
    }
}

impl<'a> Default for ParseCtx<'a> {
    fn default() -> Self {
        Self {
            _lifetime: std::marker::PhantomData,
            arena: Vec::with_capacity(Self::DEFAULT_CAPACITY),
        }
    }
}

#[derive(Debug, Lr1, PartialEq)]
pub enum NonTerminal<'a> {
    #[state(ParseCtx<'a>)]
    #[goal(r"<Expression>", reduce_goal)]
    #[production(r"<Constant>", reduce_unary_expression)]
    Expression(NodeRef<'a>),
    #[production(r"Token::IntegerConstant", reduce_constant)]
    #[production(r"Token::CharacterConstant", reduce_constant)]
    #[production(r"Token::FloatingConstant", reduce_constant)]
    Constant(NodeRef<'a>),
}

impl<'a> NonTerminalRepresentable for NonTerminal<'a> {
    type Terminal = Token<'a>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseTreeNode<'a> {
    Expression(ExprInner<'a>),
    Constant(Token<'a>),
}

pub fn parse<'a>(state: &mut ParseCtx<'a>, input: &'a str) -> Result<NonTerminal<'a>, String> {
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

    let maybe_nonterm = LrStatefulParseable::parse_input(state, tokenizer);
    maybe_nonterm
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
            let mut state = ParseCtx::default();
            let maybe_parse_tree = parse(&mut state, &input);

            assert!(maybe_parse_tree.is_ok());
            assert_eq!(state.nodes(), 2);
        }
    }
}
