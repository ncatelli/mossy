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
        )) => Ok(ParseTreeNode::Constant(term)),

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
fn reduce_inc_dec_postfix_expression<'a>(
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
    // If the expression unwraps, the oper is guranteed safe to unwrap due to
    // ensuring the stack depth is atleast 2.
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
fn reduce_struct_member_postfix_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    let maybe_third_elem = elems.pop();
    let maybe_second_elem = elems.pop();
    let maybe_expr = elems.pop();

    let postfix_expr_node_ref =
        if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Postfix(postfix_expr_node_ref))) =
            maybe_expr
        {
            Ok(postfix_expr_node_ref)
        } else {
            Err("expected postfix non-terminal 3rd from top of stack".to_string())
        }?;
    // If the expression unwraps, the second and third elem are safe to unwrap
    // due to ensuring the stack depth is atleast 3.
    let second_elem = maybe_second_elem.unwrap();
    let third_elem = maybe_third_elem.unwrap();

    let new_node = match [second_elem, third_elem] {
        [TermOrNonTerm::Terminal(Token {
            kind: TokenKind::Dot,
            ..
        }), TermOrNonTerm::Terminal(
            ident_tok @ Token {
                kind: TokenKind::Identifier,
                data: Some(_),
                ..
            },
        )] => Ok(ParseTreeNode::StructureMember {
            struct_expr: postfix_expr_node_ref,
            member_ident: ident_tok,
        }),
        [TermOrNonTerm::Terminal(Token {
            kind: TokenKind::Arrow,
            ..
        }), TermOrNonTerm::Terminal(
            ident_tok @ Token {
                kind: TokenKind::Identifier,
                data: Some(_),
                ..
            },
        )] => Ok(ParseTreeNode::StructurePointerMember {
            struct_expr: postfix_expr_node_ref,
            member_ident: ident_tok,
        }),
        top_of_stack => Err(format!(
            "expected [postfix expression, ./->, identifier] at top of stack.\nfound: {:?}",
            &top_of_stack
        )),
    }?;

    let new_node_ref = state.add_node_mut(new_node);
    Ok(NonTerminal::Postfix(new_node_ref))
}

#[allow(unused)]
fn reduce_call_postfix_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    let maybe_rparen = elems.pop();
    let maybe_lparen = elems.pop();
    let maybe_expr = elems.pop();

    if let [Some(TerminalOrNonTerminal::Terminal(Token {
        kind: TokenKind::LeftParen,
        ..
    })), Some(TerminalOrNonTerminal::Terminal(Token {
        kind: TokenKind::RightParen,
        ..
    }))] = [maybe_lparen, maybe_rparen]
    {
        Ok(())
    } else {
        Err("expected [(, )] at top of stack".to_string())
    }?;

    // unpack the lhs expressions.
    let postfix_expr_node_ref =
        if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Postfix(postfix_expr_node_ref))) =
            maybe_expr
        {
            Ok(postfix_expr_node_ref)
        } else {
            Err("expected postfix non-terminal 3rd from top of stack".to_string())
        }?;

    let new_node = ParseTreeNode::Call {
        expr: postfix_expr_node_ref,
        argument_expression_list: None,
    };

    let new_node_ref = state.add_node_mut(new_node);
    Ok(NonTerminal::Postfix(new_node_ref))
}

#[allow(unused)]
fn reduce_call_with_argument_expression_list_postfix_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    let maybe_rparen = elems.pop();
    let maybe_argument_list_expression = elems.pop();
    let maybe_lparen = elems.pop();
    let maybe_expr = elems.pop();

    let argument_list_expression_node_ref = if let [Some(TerminalOrNonTerminal::Terminal(Token {
        kind: TokenKind::LeftParen,
        ..
    })), Some(TerminalOrNonTerminal::NonTerminal(
        NonTerminal::ArgumentExpressionList(argument_list_node_ref),
    )), Some(TerminalOrNonTerminal::Terminal(Token {
        kind: TokenKind::RightParen,
        ..
    }))] =
        [maybe_lparen, maybe_argument_list_expression, maybe_rparen]
    {
        Ok(argument_list_node_ref)
    } else {
        Err("expected [(, argument expression list, )] at top of stack".to_string())
    }?;

    // unpack the lhs and index expressions.
    let postfix_expr_node_ref =
        if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Postfix(postfix_expr_node_ref))) =
            maybe_expr
        {
            Ok(postfix_expr_node_ref)
        } else {
            Err("expected postfix non-terminal 3rd from top of stack".to_string())
        }?;

    let new_node = ParseTreeNode::Call {
        expr: postfix_expr_node_ref,
        argument_expression_list: Some(argument_list_expression_node_ref),
    };

    let new_node_ref = state.add_node_mut(new_node);
    Ok(NonTerminal::Postfix(new_node_ref))
}

#[allow(unused)]
fn reduce_subscript_postfix_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    let maybe_rbracket = elems.pop();
    let maybe_index_expr = elems.pop();
    let maybe_lbracket = elems.pop();
    let maybe_expr = elems.pop();

    // check for bracket index wrappers.
    if let [Some(TerminalOrNonTerminal::Terminal(Token {
        kind: TokenKind::LeftBracket,
        ..
    })), Some(TerminalOrNonTerminal::Terminal(Token {
        kind: TokenKind::RightBracket,
        ..
    }))] = [maybe_lbracket, maybe_rbracket]
    {
        Ok(())
    } else {
        Err("expected index expression non-terminal to be l and r bracket wrapped".to_string())
    }?;

    // unpack the lhs and index expressions.
    let postfix_expr_node_ref =
        if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Postfix(postfix_expr_node_ref))) =
            maybe_expr
        {
            Ok(postfix_expr_node_ref)
        } else {
            Err("expected postfix non-terminal 4rd from top of stack".to_string())
        }?;

    let index_expr_node_ref =
        if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Expression(index_expr_node_ref))) =
            maybe_index_expr
        {
            Ok(postfix_expr_node_ref)
        } else {
            Err("expected expression non-terminal 2rd from top of stack".to_string())
        }?;

    let new_node = ParseTreeNode::Subscript {
        expr: postfix_expr_node_ref,
        subscript_expr: index_expr_node_ref,
    };

    let new_node_ref = state.add_node_mut(new_node);
    Ok(NonTerminal::Postfix(new_node_ref))
}

#[allow(unused)]
fn reduce_argument_expression_list_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Assignment(node_ref))) = elems.pop() {
        Ok(NonTerminal::ArgumentExpressionList(node_ref))
    } else {
        Err("expected assignment non-terminal at top of stack".to_string())
    }
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
fn reduce_inc_dec_unary_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    let maybe_expr = elems.pop();
    let maybe_oper = elems.pop();

    let expr_node =
        if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Unary(expr_node))) = maybe_expr {
            Ok(expr_node)
        } else {
            Err("expected nonterminal at top of stack".to_string())
        }?;

    let new_node = match maybe_oper {
        Some(TermOrNonTerm::Terminal(
            tok @ Token {
                kind: TokenKind::PlusPlus,
                ..
            },
        )) => Ok(ParseTreeNode::PreIncrement(expr_node)),
        Some(TermOrNonTerm::Terminal(
            tok @ Token {
                kind: TokenKind::MinusMinus,
                ..
            },
        )) => Ok(ParseTreeNode::PreDecrement(expr_node)),
        top_of_stack => Err(format!(
            "expected [++/--, unary expression] at top of stack.\nfound: {:?}",
            &top_of_stack
        )),
    }?;

    let new_node_ref = state.add_node_mut(new_node);
    Ok(NonTerminal::Unary(new_node_ref))
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
fn reduce_multiplicative_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Cast(node_ref))) = elems.pop() {
        Ok(NonTerminal::Multiplicative(node_ref))
    } else {
        Err("expected cast non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_additive_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Multiplicative(node_ref))) = elems.pop() {
        Ok(NonTerminal::Additive(node_ref))
    } else {
        Err("expected multiplicative non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_shift_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Additive(node_ref))) = elems.pop() {
        Ok(NonTerminal::Shift(node_ref))
    } else {
        Err("expected aditive non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_relational_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Shift(node_ref))) = elems.pop() {
        Ok(NonTerminal::Relational(node_ref))
    } else {
        Err("expected shift non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_equality_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Relational(node_ref))) = elems.pop() {
        Ok(NonTerminal::Equality(node_ref))
    } else {
        Err("expected Relational non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_and_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Equality(node_ref))) = elems.pop() {
        Ok(NonTerminal::And(node_ref))
    } else {
        Err("expected equality non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_exclusive_or_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::And(node_ref))) = elems.pop() {
        Ok(NonTerminal::ExclusiveOr(node_ref))
    } else {
        Err("expected and non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_inclusive_or_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::ExclusiveOr(node_ref))) = elems.pop() {
        Ok(NonTerminal::InclusiveOr(node_ref))
    } else {
        Err("expected exclusive or non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_logical_and_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::InclusiveOr(node_ref))) = elems.pop() {
        Ok(NonTerminal::LogicalAnd(node_ref))
    } else {
        Err("expected inclusive or non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_logical_or_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::LogicalAnd(node_ref))) = elems.pop() {
        Ok(NonTerminal::LogicalOr(node_ref))
    } else {
        Err("expected logical and non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_conditional_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::LogicalOr(node_ref))) = elems.pop() {
        Ok(NonTerminal::Conditional(node_ref))
    } else {
        Err("expected logical or non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_assignment_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Conditional(node_ref))) = elems.pop() {
        Ok(NonTerminal::Assignment(node_ref))
    } else {
        Err("expected conditional non-terminal at top of stack".to_string())
    }
}

#[allow(unused)]
fn reduce_expression<'a>(
    state: &mut ParseCtx<'a>,
    elems: &mut Vec<TermOrNonTerm<'a>>,
) -> Result<NonTerminal<'a>, String> {
    if let Some(TermOrNonTerm::NonTerminal(NonTerminal::Assignment(node_ref))) = elems.pop() {
        Ok(NonTerminal::Expression(node_ref))
    } else {
        Err("expected assignment non-terminal at top of stack".to_string())
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
    #[production(r"<Assignment>", reduce_expression)]
    Expression(NodeRef<'a>),

    #[production(r"<Conditional>", reduce_assignment_expression)]
    Assignment(NodeRef<'a>),

    #[production(r"<LogicalOr>", reduce_conditional_expression)]
    Conditional(NodeRef<'a>),

    #[production(r"<LogicalAnd>", reduce_logical_or_expression)]
    LogicalOr(NodeRef<'a>),

    #[production(r"<InclusiveOr>", reduce_logical_and_expression)]
    LogicalAnd(NodeRef<'a>),

    #[production(r"<ExclusiveOr>", reduce_inclusive_or_expression)]
    InclusiveOr(NodeRef<'a>),

    #[production(r"<And>", reduce_exclusive_or_expression)]
    ExclusiveOr(NodeRef<'a>),

    #[production(r"<Equality>", reduce_and_expression)]
    And(NodeRef<'a>),

    #[production(r"<Relational>", reduce_equality_expression)]
    Equality(NodeRef<'a>),

    #[production(r"<Shift>", reduce_relational_expression)]
    Relational(NodeRef<'a>),

    #[production(r"<Additive>", reduce_shift_expression)]
    Shift(NodeRef<'a>),

    #[production(r"<Multiplicative>", reduce_additive_expression)]
    Additive(NodeRef<'a>),

    #[production(r"<Cast>", reduce_multiplicative_expression)]
    Multiplicative(NodeRef<'a>),

    #[production(r"<Unary>", reduce_cast_expression)]
    Cast(NodeRef<'a>),

    #[production(r"<Postfix>", reduce_unary_expression)]
    #[production(r"Token::PlusPlus <Unary>", reduce_inc_dec_unary_expression)]
    #[production(r"Token::MinusMinus <Unary>", reduce_inc_dec_unary_expression)]
    Unary(NodeRef<'a>),

    #[production(r"<Primary>", reduce_primary_to_postfix_expression)]
    #[production(
        r"<Postfix> Token::LeftBracket <Expression> Token::RightBracket",
        reduce_subscript_postfix_expression
    )]
    #[production(
        r"<Postfix> Token::LeftParen Token::RightParen",
        reduce_call_postfix_expression
    )]
    #[production(
        r"<Postfix> Token::LeftParen <ArgumentExpressionList> Token::RightParen",
        reduce_call_with_argument_expression_list_postfix_expression
    )]
    #[production(
        r"<Postfix> Token::Dot Token::Identifier",
        reduce_struct_member_postfix_expression
    )]
    #[production(
        r"<Postfix> Token::Arrow Token::Identifier",
        reduce_struct_member_postfix_expression
    )]
    #[production(r"<Postfix> Token::PlusPlus", reduce_inc_dec_postfix_expression)]
    #[production(r"<Postfix> Token::MinusMinus", reduce_inc_dec_postfix_expression)]
    Postfix(NodeRef<'a>),

    #[production(r"<Assignment>", reduce_argument_expression_list_expression)]
    ArgumentExpressionList(NodeRef<'a>),

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
    /* TODO: EnumerationConstant is not implemented yet.
    #[production(r"Token::EnumerationConstant", reduce_constant)]
    */
    Constant(NodeRef<'a>),
}

impl<'a> NonTerminalRepresentable for NonTerminal<'a> {
    type Terminal = Token<'a>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseTreeNode<'a> {
    // ++<expression>
    PreIncrement(NodeRef<'a>),
    // --<expression>
    PreDecrement(NodeRef<'a>),

    // <expr>[<index expr>]
    Subscript {
        expr: NodeRef<'a>,
        subscript_expr: NodeRef<'a>,
    },
    // <expr>()
    Call {
        expr: NodeRef<'a>,
        argument_expression_list: Option<NodeRef<'a>>,
    },
    // <struct expr>.<ident>
    StructureMember {
        struct_expr: NodeRef<'a>,
        member_ident: Token<'a>,
    },

    // <struct expr>-><ident>
    StructurePointerMember {
        struct_expr: NodeRef<'a>,
        member_ident: Token<'a>,
    },

    // <expression>++
    PostIncrement(NodeRef<'a>),
    // <expression>--
    PostDecrement(NodeRef<'a>),
    Grouping(NodeRef<'a>),
    Identifer(Token<'a>),
    StringLiteral(Token<'a>),
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

    LrStatefulParseable::parse_input(state, tokenizer)
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_node_at_index_is_generated_from {
        ($input:expr, $expected_node_offset:literal, $expected_node_kind:pat) => {
            let mut state = ParseCtx::default();
            let maybe_parse_tree = parse(&mut state, &$input);

            assert!(maybe_parse_tree.is_ok());

            let expr_node = &state.arena[$expected_node_offset];

            assert!(matches!(expr_node, $expected_node_kind), "{:?}", expr_node);
        };
    }

    #[test]
    fn should_parse_unary_expression() {
        // pre-increment
        assert_node_at_index_is_generated_from!("++5", 1, ParseTreeNode::PreIncrement { .. });
        // pre-decrement
        assert_node_at_index_is_generated_from!("--5", 1, ParseTreeNode::PreDecrement { .. });
    }

    #[test]
    fn should_parse_postfix_expression() {
        // post increment
        assert_node_at_index_is_generated_from!("5++", 1, ParseTreeNode::PostIncrement { .. });
        // post decrement
        assert_node_at_index_is_generated_from!("5--", 1, ParseTreeNode::PostDecrement { .. });

        // struct member of
        assert_node_at_index_is_generated_from!(
            "hello.world",
            1,
            ParseTreeNode::StructureMember { .. }
        );
        assert_node_at_index_is_generated_from!(
            "hello->world",
            1,
            ParseTreeNode::StructurePointerMember { .. }
        );

        // subscript
        assert_node_at_index_is_generated_from!("hello[0]", 2, ParseTreeNode::Subscript { .. });

        // call
        assert_node_at_index_is_generated_from!("hello()", 1, ParseTreeNode::Call { .. });
        assert_node_at_index_is_generated_from!(
            "hello(5)",
            2,
            ParseTreeNode::Call {
                expr: NodeRef { idx: 0, .. },
                argument_expression_list: Some(NodeRef { idx: 1, .. })
            }
        );
    }

    #[test]
    fn should_parse_primary_grouping_expression() {
        assert_node_at_index_is_generated_from!(
            "( test )",
            0,
            ParseTreeNode::Identifer(Token {
                kind: TokenKind::Identifier,
                ..
            })
        );
        assert_node_at_index_is_generated_from!("( test )", 1, ParseTreeNode::Grouping(_));

        // nested grouping
        assert_node_at_index_is_generated_from!(
            "(( test ))",
            0,
            ParseTreeNode::Identifer(Token {
                kind: TokenKind::Identifier,
                ..
            })
        );
        assert_node_at_index_is_generated_from!("(( test ))", 1, ParseTreeNode::Grouping(_));
    }

    #[test]
    fn should_parse_primary_expression() {
        // string literal
        assert_node_at_index_is_generated_from!(
            "\"hello world\"",
            0,
            ParseTreeNode::StringLiteral(Token {
                kind: TokenKind::StringLiteral,
                data: Some("hello world"),
                ..
            })
        );

        // identifier
        assert_node_at_index_is_generated_from!(
            "test",
            0,
            ParseTreeNode::Identifer(Token {
                kind: TokenKind::Identifier,
                data: Some("test"),
                ..
            })
        );
    }

    #[test]
    fn should_parse_standalone_constants() {
        assert_node_at_index_is_generated_from!(
            "5",
            0,
            ParseTreeNode::Constant(Token {
                kind: TokenKind::IntegerConstant,
                data: Some("5"),
                ..
            })
        );

        assert_node_at_index_is_generated_from!(
            "\'c\'",
            0,
            ParseTreeNode::Constant(Token {
                kind: TokenKind::CharacterConstant,
                data: Some("c"),
                ..
            })
        );

        assert_node_at_index_is_generated_from!(
            "5.0",
            0,
            ParseTreeNode::Constant(Token {
                kind: TokenKind::FloatingConstant,
                data: Some("5.0"),
                ..
            })
        );
    }

    #[test]
    fn should_retain_expected_parse_tree_component_sizes() {
        assert_eq!(std::mem::size_of::<NonTerminal>(), 16);
        assert_eq!(std::mem::size_of::<ParseTreeNode>(), 88);
    }
}
