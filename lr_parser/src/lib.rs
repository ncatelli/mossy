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

type TermOrNonTerm<'a> = TerminalOrNonTerminal<Token<'a>, NonTerminal<'a>>;

/// Caller assumes
#[allow(unused)]
fn reduce_constant<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    let node = match elems.pop() {
        Some(TermOrNonTerm::Terminal(
            term @ Token {
                kind: TokenKind::IntegerConstant,
                ..
            },
        )) => Ok(ParseTreeNode::IntegerConstant(term)),
        Some(TermOrNonTerm::Terminal(
            term @ Token {
                kind: TokenKind::CharacterConstant,
                ..
            },
        )) => Ok(ParseTreeNode::CharacterConstant(term)),
        Some(TermOrNonTerm::Terminal(
            term @ Token {
                kind: TokenKind::FloatingConstant,
                ..
            },
        )) => Ok(ParseTreeNode::FloatConstant(term)),

        _ => Err("expected constant terminal at top of stack".to_string()),
    }?;

    let nt_ref = state.add_node_mut(node);

    Ok(NonTerminal::Constant(nt_ref))
}

#[allow(unused)]
fn reduce_primary_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    match elems.pop() {
        // constants
        Some(TermOrNonTerm::NonTerminal(NonTerminal::Constant(node_ref))) => {
            Ok(NonTerminal::Primary(node_ref))
        }

        // identifer
        Some(TerminalOrNonTerminal::Terminal(
            term @ Token {
                kind: TokenKind::Identifier,
                ..
            },
        )) => {
            let node = ParseTreeNode::Identifer(term);
            let node_ref = state.add_node_mut(node);

            Ok(NonTerminal::Primary(node_ref))
        }

        // string literal
        Some(TerminalOrNonTerminal::Terminal(
            term @ Token {
                kind: TokenKind::StringLiteral,
                ..
            },
        )) => {
            let node = ParseTreeNode::StringLiteral(term);
            let node_ref = state.add_node_mut(node);

            Ok(NonTerminal::Primary(node_ref))
        }
        _ => Err("expected non-terminal at top of stack".to_string()),
    }
}

#[allow(unused)]
fn reduce_primary_grouping_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    let maybe_rparen = elems.pop();
    let maybe_expression = elems.pop();
    let maybe_lparen = elems.pop();

    if let [Some(TermOrNonTerm::Terminal(Token {
        kind: TokenKind::LeftParen,
        ..
    })), Some(TermOrNonTerm::NonTerminal(NonTerminal::Expression(node_ref))), Some(TermOrNonTerm::Terminal(Token {
        kind: TokenKind::RightParen,
        ..
    }))] = [maybe_lparen, maybe_expression, maybe_rparen]
    {
        let node = ParseTreeNode::Grouping(node_ref);
        let new_node_ref = state.add_node_mut(node);

        Ok(NonTerminal::Primary(new_node_ref))
    } else {
        Err("expected `(` + <Expression> + `)` at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_primary_to_postfix_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Primary(node_ref))) = elems.pop() {
        Ok(NonTerminal::Postfix(node_ref))
    } else {
        Err("expected primary non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_postfix_two_element_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    let maybe_oper = elems.pop();
    let maybe_expr = elems.pop();

    let postfix_expr_node_ref =
        if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Postfix(postfix_expr_node_ref))) =
            maybe_expr
        {
            Ok(postfix_expr_node_ref)
        } else {
            Err("expected nonterminal 2nd from top of stack".to_string())
        }?;
    // If the expression unwraps, the oper is guaranteed to exist and is safe
    // to unwrap.
    let oper = maybe_oper.unwrap();

    let new_node = match oper {
        TermOrNonTerm::Terminal(
            tok @ Token {
                kind: TokenKind::PlusPlus,
                ..
            },
        ) => Ok(ParseTreeNode::PostIncrement(postfix_expr_node_ref)),
        TermOrNonTerm::Terminal(
            tok @ Token {
                kind: TokenKind::MinusMinus,
                ..
            },
        ) => Ok(ParseTreeNode::PostDecrement(postfix_expr_node_ref)),
        top_of_stack => Err(format!(
            "expected [postfix expression, ++/--] at top of stack.\nfound: {:?}",
            &top_of_stack
        )),
    }?;

    let new_node_ref = state.add_node_mut(new_node);
    Ok(NonTerminal::Postfix(new_node_ref))
}

#[allow(unused)]
fn reduce_unary_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Postfix(node_ref))) = elems.pop() {
        Ok(NonTerminal::Unary(node_ref))
    } else {
        Err("expected postfix non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_cast_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Unary(node_ref))) = elems.pop() {
        Ok(NonTerminal::Cast(node_ref))
    } else {
        Err("expected unary non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Cast(node_ref))) = elems.pop() {
        Ok(NonTerminal::Expression(node_ref))
    } else {
        Err("expected cast non-terminal at top of stack".to_string())
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
    #[production(r"<Cast>", reduce_expression)]
    Expression(NodeRef<'a>),

    #[production(r"<Unary>", reduce_cast_expression)]
    Cast(NodeRef<'a>),

    #[production(r"<Postfix>", reduce_unary_expression)]
    Unary(NodeRef<'a>),

    #[production(r"<Primary>", reduce_primary_to_postfix_expression)]
    #[production(r"<Postfix> Token::PlusPlus", reduce_postfix_two_element_expression)]
    #[production(r"<Postfix> Token::MinusMinus", reduce_postfix_two_element_expression)]
    Postfix(NodeRef<'a>),

    #[production(r"Token::Identifier", reduce_primary_expression)]
    #[production(r"<Constant>", reduce_primary_expression)]
    #[production(r"Token::StringLiteral", reduce_primary_expression)]
    #[production(
        r"Token::LeftParen <Expression> Token::RightParen",
        reduce_primary_grouping_expression
    )]
    Primary(NodeRef<'a>),

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
    Grouping(NodeRef<'a>),
    Identifer(Token<'a>),
    PostIncrement(NodeRef<'a>),
    PostDecrement(NodeRef<'a>),
    StringLiteral(Token<'a>),
    IntegerConstant(Token<'a>),
    CharacterConstant(Token<'a>),
    FloatConstant(Token<'a>),
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

    LrStatefulParseable::parse_input(state, tokenizer)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_parse_postfix_expression() {
        // nested grouping
        let input = "5++";

        let mut state = ParseCtx::default();
        let maybe_parse_tree = parse(&mut state, &input);

        assert!(maybe_parse_tree.is_ok());

        let postfix_expr_node = &state.arena[1];

        assert!(
            matches!(postfix_expr_node, ParseTreeNode::PostIncrement(_)),
            "{:?}",
            postfix_expr_node
        );
    }

    #[test]
    fn should_parse_primary_grouping_expression() {
        // nested grouping
        let input = "(( test ))";

        let mut state = ParseCtx::default();
        let maybe_parse_tree = parse(&mut state, &input);

        assert!(maybe_parse_tree.is_ok());

        let constant_expr_node = &state.arena[0];

        assert!(matches!(
            &constant_expr_node,
            ParseTreeNode::Identifer(Token {
                kind: TokenKind::Identifier,
                ..
            })
        ));
    }

    #[test]
    fn should_parse_primary_expression() {
        let inputs = [
            "\"hello world\"", // string literal
            "test",            // identifier
        ];

        let mut nodes = Vec::new();
        for input in inputs {
            let mut state = ParseCtx::default();
            let maybe_parse_tree = parse(&mut state, &input);

            assert!(maybe_parse_tree.is_ok(), "{:?}", &maybe_parse_tree);

            // leaf of parse tree.
            let node = &state.arena[0];
            nodes.push(node.clone());
        }
        // assert first result is a string literal.
        assert!(matches!(
            &nodes[0],
            ParseTreeNode::StringLiteral(Token {
                kind: TokenKind::StringLiteral,
                data: Some("hello world"),
                ..
            })
        ),);

        // assert second result is an identifier.
        assert!(matches!(
            &nodes[1],
            ParseTreeNode::Identifer(Token {
                kind: TokenKind::Identifier,
                data: Some("test"),
                ..
            })
        ));
    }

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
            assert_eq!(state.nodes(), 1);
        }
    }

    #[test]
    fn should_retain_expected_parse_tree_component_sizes() {
        assert_eq!(std::mem::size_of::<NonTerminal>(), 16);
        assert_eq!(std::mem::size_of::<ParseTreeNode>(), 80);
    }
}
