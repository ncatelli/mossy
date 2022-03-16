use parcel::parsers::character::*;
use parcel::prelude::v1::*;

use crate::lexer::{Token, TokenType};

pub use crate::stage::type_check::ast::Type;
use crate::stage::type_check::{
    self,
    ast::{IntegerWidth, Signed},
};

use super::ast::{self, *};

/// ParseErr represents a parser response that doesn't return a correct AstNode.
#[derive(Debug, Clone, PartialEq)]
pub enum ParseErr {
    UnexpectedToken(String),
    Unspecified(String),
}

/// parse expects a character slice as input and attempts to parse a valid
/// expression, returning a parse error if it is invalid.
pub fn parse(input: &[(usize, char)]) -> Result<CompilationUnit, ParseErr> {
    parcel::one_or_more(
        function_definition()
            .map(ast::GlobalDecls::FuncDefinition)
            .or(|| {
                parcel::left(parcel::join(
                    function_prototype(),
                    whitespace_wrapped(expect_character(';')),
                ))
                .map(ast::GlobalDecls::FuncProto)
            })
            .or(|| {
                semicolon_terminated_statement(declaration()).map(|stmt| {
                    // safe to unpack due to declaration guarantee.
                    if let ast::StmtNode::Declaration(decl) = stmt {
                        ast::GlobalDecls::Var(decl)
                    } else {
                        unreachable!()
                    }
                })
            }),
    )
    .parse(input)
    .map_err(ParseErr::UnexpectedToken)
    .and_then(|ms| match ms {
        MatchStatus::Match {
            span: _,
            remainder: _,
            inner,
        } => Ok(inner),
        MatchStatus::NoMatch(_) => Err(ParseErr::Unspecified("not a valid expression".to_string())),
    })
    .map(CompilationUnit::new)
}

fn function_prototype<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], FunctionProto> {
    parcel::join(
        parcel::join(type_declarator(), whitespace_wrapped(identifier())),
        expect_character('(').and_then(|_| {
            parcel::left(parcel::join(
                parcel::join(
                    parcel::zero_or_more(
                        parcel::join(
                            whitespace_wrapped(type_declarator()),
                            parcel::left(parcel::join(
                                identifier(),
                                whitespace_wrapped(expect_character(',')),
                            )),
                        )
                        .map(|(ty, id)| ast::Parameter::new(id, ty)),
                    ),
                    parcel::join(whitespace_wrapped(type_declarator()), identifier())
                        .map(|(ty, id)| ast::Parameter::new(id, ty)),
                )
                .map(|(mut head, tail)| {
                    head.push(tail);
                    head
                })
                .or(|| {
                    parcel::zero_or_more(
                        parcel::join(whitespace_wrapped(type_declarator()), identifier())
                            .map(|(ty, id)| ast::Parameter::new(id, ty)),
                    )
                }),
                whitespace_wrapped(expect_character(')')),
            ))
        }),
    )
    .map(|((ty, id), params)| FunctionProto::new(id, ty, params))
}

fn function_definition<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], FunctionDefinition> {
    parcel::join(function_prototype(), compound_statements())
        .map(|(proto, block)| FunctionDefinition::new(proto, block))
}

fn compound_statements<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], CompoundStmts> {
    character_wrapped('{', '}', parcel::zero_or_more(statement())).map(CompoundStmts::new)
}

fn statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    semicolon_terminated_statement(declaration())
        .or(if_statement)
        .or(while_statement)
        .or(for_statement)
        .or(|| semicolon_terminated_statement(return_statement()))
        .or(|| semicolon_terminated_statement(expression().map(StmtNode::Expression)))
}

fn semicolon_terminated_statement<'a, P>(
    term: P,
) -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode>
where
    P: parcel::Parser<'a, &'a [(usize, char)], StmtNode> + 'a,
{
    parcel::left(parcel::join(
        term,
        whitespace_wrapped(expect_character(';')),
    ))
}

fn declaration<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    parcel::join(
        type_declarator(),
        whitespace_wrapped(parcel::join(
            identifier(),
            character_wrapped('[', ']', unsigned_number()),
        )),
    )
    .map(|(ty, (id, size))| {
        let size = match size {
            Primary::Integer {
                value,
                sign: Signed::Unsigned,
                ..
            } => usize::from_le_bytes(value),
            // The remaining three variants are guaranteed to be unreachable by
            // the parser.
            _ => unreachable!(),
        };
        (ty, id, size)
    })
    .map(|(ty, id, size)| type_check::ast::Declaration::Array { ty, id, size })
    .map(StmtNode::Declaration)
    .or(|| {
        parcel::join(
            type_declarator(),
            whitespace_wrapped(parcel::one_or_more(parcel::left(parcel::join(
                identifier(),
                whitespace_wrapped(expect_character(',').optional()),
            )))),
        )
        .map(|(ty, ids)| type_check::ast::Declaration::Scalar(ty, ids))
        .map(StmtNode::Declaration)
    })
}

fn if_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    parcel::join(
        if_head(),
        parcel::optional(
            whitespace_wrapped(expect_str("else")).and_then(|_| compound_statements()),
        ),
    )
    .map(|((cond, cond_true), cond_false)| StmtNode::If(cond, cond_true, cond_false))
}

fn if_head<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], (ExprNode, CompoundStmts)> {
    whitespace_wrapped(expect_str("if")).and_then(|_| {
        parcel::join(
            character_wrapped('(', ')', expression()),
            compound_statements(),
        )
    })
}

fn while_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    whitespace_wrapped(expect_str("while"))
        .and_then(|_| {
            parcel::join(
                character_wrapped('(', ')', expression()),
                compound_statements(),
            )
        })
        .map(|(cond, block)| StmtNode::While(cond, block))
}

fn for_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    whitespace_wrapped(expect_str("for"))
        .and_then(|_| {
            parcel::join(
                character_wrapped(
                    '(',
                    ')',
                    parcel::join(
                        parcel::left(parcel::join(
                            preop_statement(),
                            whitespace_wrapped(expect_character(';')),
                        )),
                        parcel::join(
                            parcel::left(parcel::join(
                                expression(),
                                whitespace_wrapped(expect_character(';')),
                            )),
                            postop_statement(),
                        ),
                    ),
                ),
                compound_statements(),
            )
        })
        .map(|((preop, (cond, postop)), block)| {
            StmtNode::For(Box::new(preop), cond, Box::new(postop), block)
        })
}

fn preop_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    assignment().map(StmtNode::Expression)
}

fn postop_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    expression().map(StmtNode::Expression)
}

fn return_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    parcel::right(parcel::join(
        whitespace_wrapped(expect_str("return")),
        expression().optional(),
    ))
    .map(StmtNode::Return)
}

fn expression<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    assignment()
}

fn new_expression<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    new_assignment()
}

fn assignment<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        whitespace_wrapped(logical()),
        whitespace_wrapped(expect_character('=')).and_then(|_| whitespace_wrapped(assignment())),
    )
    .map(|(lhs, rhs)| assignment_expr!(lhs, '=', rhs))
    .or(logical)
}

fn new_assignment<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        new_logical(),
        expect_tokentype(TokenType::Equal).and_then(|_| new_assignment()),
    )
    .map(|(lhs, rhs)| assignment_expr!(lhs, '=', rhs))
    .or(new_logical)
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum LogicalExprOp {
    Or,
    And,
}

fn logical<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        bitwise(),
        parcel::zero_or_more(parcel::join(
            whitespace_wrapped(expect_str("||"))
                .map(|_| LogicalExprOp::Or)
                .or(|| whitespace_wrapped(expect_str("&&")).map(|_| LogicalExprOp::And)),
            whitespace_wrapped(bitwise()),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                LogicalExprOp::Or => binary_logical_expr!(lhs, "||", rhs),
                LogicalExprOp::And => binary_logical_expr!(lhs, "&&", rhs),
            })
    })
}

fn new_logical<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        new_bitwise(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::PipePipe)
                .map(|_| LogicalExprOp::Or)
                .or(|| expect_tokentype(TokenType::AmpersandAmpersand).map(|_| LogicalExprOp::And)),
            new_bitwise(),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                LogicalExprOp::Or => binary_logical_expr!(lhs, "||", rhs),
                LogicalExprOp::And => binary_logical_expr!(lhs, "&&", rhs),
            })
    })
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum BitwiseExprOp {
    Or,
    Xor,
    And,
}

fn bitwise<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        equality(),
        parcel::zero_or_more(parcel::join(
            whitespace_wrapped(
                expect_str("|")
                    .peek_next(any_character().predicate(|&c| c != '|'))
                    .map(|_| BitwiseExprOp::Or)
                    .or(|| expect_str("^").map(|_| BitwiseExprOp::Xor))
                    .or(|| {
                        expect_str("&")
                            .peek_next(any_character().predicate(|&c| c != '&'))
                            .map(|_| BitwiseExprOp::And)
                    }),
            ),
            whitespace_wrapped(equality()),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                BitwiseExprOp::Or => bitwise_expr!(lhs, "|", rhs),
                BitwiseExprOp::Xor => bitwise_expr!(lhs, "^", rhs),
                BitwiseExprOp::And => bitwise_expr!(lhs, "&", rhs),
            })
    })
}

fn new_bitwise<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        new_equality(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::Pipe)
                .map(|_| BitwiseExprOp::Or)
                .or(|| expect_tokentype(TokenType::Carat).map(|_| BitwiseExprOp::Xor))
                .or(|| expect_tokentype(TokenType::Ampersand).map(|_| BitwiseExprOp::And)),
            new_equality(),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                BitwiseExprOp::Or => bitwise_expr!(lhs, "|", rhs),
                BitwiseExprOp::Xor => bitwise_expr!(lhs, "^", rhs),
                BitwiseExprOp::And => bitwise_expr!(lhs, "&", rhs),
            })
    })
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum EqualityExprOp {
    Equal,
    NotEqual,
}

fn equality<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        relational(),
        parcel::zero_or_more(parcel::join(
            whitespace_wrapped(
                expect_str("==")
                    .map(|_| EqualityExprOp::Equal)
                    .or(|| expect_str("!=").map(|_| EqualityExprOp::NotEqual)),
            ),
            whitespace_wrapped(relational()),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                EqualityExprOp::Equal => equality_expr!(lhs, "==", rhs),
                EqualityExprOp::NotEqual => equality_expr!(lhs, "!=", rhs),
            })
    })
}

fn new_equality<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        new_relational(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::EqualEqual)
                .map(|_| EqualityExprOp::Equal)
                .or(|| expect_tokentype(TokenType::BangEqual).map(|_| EqualityExprOp::NotEqual)),
            new_relational(),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                EqualityExprOp::Equal => equality_expr!(lhs, "==", rhs),
                EqualityExprOp::NotEqual => equality_expr!(lhs, "!=", rhs),
            })
    })
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum RelationalExprOp {
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

fn relational<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        bitwise_shift(),
        parcel::zero_or_more(parcel::join(
            whitespace_wrapped(
                expect_str("<=")
                    .map(|_| RelationalExprOp::LessEqual)
                    .or(|| expect_str(">=").map(|_| RelationalExprOp::GreaterEqual))
                    .or(|| expect_str("<").map(|_| RelationalExprOp::LessThan))
                    .or(|| expect_str(">").map(|_| RelationalExprOp::GreaterThan)),
            ),
            whitespace_wrapped(bitwise_shift()),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                RelationalExprOp::LessThan => ExprNode::LessThan(Box::new(lhs), Box::new(rhs)),
                RelationalExprOp::LessEqual => ExprNode::LessEqual(Box::new(lhs), Box::new(rhs)),
                RelationalExprOp::GreaterThan => {
                    ExprNode::GreaterThan(Box::new(lhs), Box::new(rhs))
                }
                RelationalExprOp::GreaterEqual => {
                    ExprNode::GreaterEqual(Box::new(lhs), Box::new(rhs))
                }
            })
    })
}

fn new_relational<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        new_bitwise_shift(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::LessEqual)
                .map(|_| RelationalExprOp::LessEqual)
                .or(|| {
                    expect_tokentype(TokenType::GreaterEqual)
                        .map(|_| RelationalExprOp::GreaterEqual)
                })
                .or(|| expect_tokentype(TokenType::LessThan).map(|_| RelationalExprOp::LessThan))
                .or(|| {
                    expect_tokentype(TokenType::GreaterThan).map(|_| RelationalExprOp::GreaterThan)
                }),
            new_bitwise_shift(),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                RelationalExprOp::LessThan => ExprNode::LessThan(Box::new(lhs), Box::new(rhs)),
                RelationalExprOp::LessEqual => ExprNode::LessEqual(Box::new(lhs), Box::new(rhs)),
                RelationalExprOp::GreaterThan => {
                    ExprNode::GreaterThan(Box::new(lhs), Box::new(rhs))
                }
                RelationalExprOp::GreaterEqual => {
                    ExprNode::GreaterEqual(Box::new(lhs), Box::new(rhs))
                }
            })
    })
}
#[derive(Debug, Clone, Copy, PartialEq)]
enum BitwiseShiftExprOp {
    ShiftLeft,
    ShiftRight,
}

fn bitwise_shift<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        addition(),
        parcel::zero_or_more(parcel::join(
            whitespace_wrapped(
                expect_str("<<")
                    .map(|_| BitwiseShiftExprOp::ShiftLeft)
                    .or(|| expect_str(">>").map(|_| BitwiseShiftExprOp::ShiftRight)),
            ),
            whitespace_wrapped(addition()),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                BitwiseShiftExprOp::ShiftLeft => bitwise_shift_expr!(lhs, "<<", rhs),
                BitwiseShiftExprOp::ShiftRight => bitwise_shift_expr!(lhs, ">>", rhs),
            })
    })
}

fn new_bitwise_shift<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        new_addition(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::LShift)
                .map(|_| BitwiseShiftExprOp::ShiftLeft)
                .or(|| expect_tokentype(TokenType::RShift).map(|_| BitwiseShiftExprOp::ShiftRight)),
            new_addition(),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                BitwiseShiftExprOp::ShiftLeft => bitwise_shift_expr!(lhs, "<<", rhs),
                BitwiseShiftExprOp::ShiftRight => bitwise_shift_expr!(lhs, ">>", rhs),
            })
    })
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum AdditionExprOp {
    Plus,
    Minus,
}

fn addition<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        multiplication(),
        parcel::zero_or_more(parcel::join(
            whitespace_wrapped(
                expect_character('+')
                    .map(|_| AdditionExprOp::Plus)
                    .or(|| expect_character('-').map(|_| AdditionExprOp::Minus)),
            ),
            whitespace_wrapped(multiplication()),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                AdditionExprOp::Plus => term_expr!(lhs, '+', rhs),
                AdditionExprOp::Minus => term_expr!(lhs, '-', rhs),
            })
    })
}

fn new_addition<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        new_multiplication(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::Plus)
                .map(|_| AdditionExprOp::Plus)
                .or(|| expect_tokentype(TokenType::Minus).map(|_| AdditionExprOp::Minus)),
            new_multiplication(),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                AdditionExprOp::Plus => term_expr!(lhs, '+', rhs),
                AdditionExprOp::Minus => term_expr!(lhs, '-', rhs),
            })
    })
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum MultiplicationExprOp {
    Star,
    Slash,
    Mod,
}

fn multiplication<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        call(),
        parcel::zero_or_more(parcel::join(
            whitespace_wrapped(
                expect_character('*')
                    .map(|_| MultiplicationExprOp::Star)
                    .or(|| expect_character('/').map(|_| MultiplicationExprOp::Slash))
                    .or(|| expect_character('%').map(|_| MultiplicationExprOp::Mod)),
            ),
            whitespace_wrapped(call()),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                MultiplicationExprOp::Star => {
                    factor_expr!(lhs, '*', rhs)
                }
                MultiplicationExprOp::Slash => factor_expr!(lhs, '/', rhs),
                MultiplicationExprOp::Mod => factor_expr!(lhs, '%', rhs),
            })
    })
}

fn new_multiplication<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        new_call(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::Star)
                .map(|_| MultiplicationExprOp::Star)
                .or(|| expect_tokentype(TokenType::Slash).map(|_| MultiplicationExprOp::Slash))
                .or(|| expect_tokentype(TokenType::PercentSign).map(|_| MultiplicationExprOp::Mod)),
            new_call(),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                MultiplicationExprOp::Star => {
                    factor_expr!(lhs, '*', rhs)
                }
                MultiplicationExprOp::Slash => factor_expr!(lhs, '/', rhs),
                MultiplicationExprOp::Mod => factor_expr!(lhs, '%', rhs),
            })
    })
}

fn call<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        identifier(),
        whitespace_wrapped(expect_character('(')).and_then(|_| {
            parcel::left(parcel::join(
                parcel::join(
                    parcel::zero_or_more(parcel::left(parcel::join(
                        expression(),
                        whitespace_wrapped(expect_character(',')),
                    ))),
                    expression(),
                )
                .map(|(mut head, tail)| {
                    head.push(tail);
                    head
                })
                .or(|| {
                    expression()
                        .optional()
                        .map(|optional_expr| match optional_expr {
                            Some(expr) => vec![expr],
                            None => vec![],
                        })
                }),
                whitespace_wrapped(expect_character(')')),
            ))
        }),
    )
    .map(|(id, exprs)| ExprNode::FunctionCall(id, exprs))
    .or(prefix_expression)
}

fn new_call<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        new_identifier(),
        expect_tokentype(TokenType::LParen).and_then(|_| {
            parcel::left(parcel::join(
                parcel::join(
                    parcel::zero_or_more(parcel::left(parcel::join(
                        new_expression(),
                        expect_tokentype(TokenType::Comma),
                    ))),
                    new_expression(),
                )
                .map(|(mut head, tail)| {
                    head.push(tail);
                    head
                })
                .or(|| {
                    new_expression()
                        .optional()
                        .map(|optional_expr| match optional_expr {
                            Some(expr) => vec![expr],
                            None => vec![],
                        })
                }),
                expect_tokentype(TokenType::RParen),
            ))
        }),
    )
    .map(|(id, exprs)| ExprNode::FunctionCall(id, exprs))
    .or(new_prefix_expression)
}

fn prefix_expression<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    whitespace_wrapped(expect_character('*'))
        .and_then(|_| prefix_expression())
        .map(Box::new)
        .map(ExprNode::Deref)
        .or(|| {
            whitespace_wrapped(expect_character('&'))
                .and_then(|_| identifier())
                .map(ExprNode::Ref)
        })
        .or(|| {
            whitespace_wrapped(expect_str("++"))
                .and_then(|_| prefix_expression())
                .map(Box::new)
                .map(ExprNode::PreIncrement)
        })
        .or(|| {
            whitespace_wrapped(expect_str("--"))
                .and_then(|_| prefix_expression())
                .map(Box::new)
                .map(ExprNode::PreDecrement)
        })
        // unary logical not
        .or(|| {
            whitespace_wrapped(expect_character('!'))
                .and_then(|_| prefix_expression())
                .map(Box::new)
                .map(ExprNode::LogicalNot)
        })
        // unary negate
        .or(|| {
            whitespace_wrapped(expect_character('-'))
                .and_then(|_| prefix_expression())
                // prevent negate from eating `-` on integer literals.
                .predicate(|e| !matches!(e, ExprNode::Primary(Primary::Integer { .. })))
                .map(Box::new)
                .map(ExprNode::Negate)
        })
        // unary inverse
        .or(|| {
            whitespace_wrapped(expect_character('~'))
                .and_then(|_| prefix_expression())
                .map(Box::new)
                .map(ExprNode::Invert)
        })
        .or(post_increment_decrement_expression)
}

fn new_prefix_expression<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    expect_tokentype(TokenType::Star)
        .and_then(|_| new_prefix_expression())
        .map(Box::new)
        .map(ExprNode::Deref)
        .or(|| {
            expect_tokentype(TokenType::Ampersand)
                .and_then(|_| new_identifier())
                .map(ExprNode::Ref)
        })
        .or(|| {
            expect_tokentype(TokenType::PlusPlus)
                .and_then(|_| new_prefix_expression())
                .map(Box::new)
                .map(ExprNode::PreIncrement)
        })
        .or(|| {
            expect_tokentype(TokenType::MinusMinus)
                .and_then(|_| new_prefix_expression())
                .map(Box::new)
                .map(ExprNode::PreDecrement)
        })
        // unary logical not
        .or(|| {
            expect_tokentype(TokenType::Bang)
                .and_then(|_| new_prefix_expression())
                .map(Box::new)
                .map(ExprNode::LogicalNot)
        })
        // unary negate
        .or(|| {
            expect_tokentype(TokenType::Minus)
                .and_then(|_| new_prefix_expression())
                // prevent negate from eating `-` on integer literals.
                .predicate(|e| !matches!(e, ExprNode::Primary(Primary::Integer { .. })))
                .map(Box::new)
                .map(ExprNode::Negate)
        })
        // unary inverse
        .or(|| {
            expect_tokentype(TokenType::Tilde)
                .and_then(|_| new_prefix_expression())
                .map(Box::new)
                .map(ExprNode::Invert)
        })
        .or(new_post_increment_decrement_expression)
}

fn post_increment_decrement_expression<'a>(
) -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::left(parcel::join(
        whitespace_wrapped(postfix_expression()),
        expect_str("++"),
    ))
    .map(Box::new)
    .map(ExprNode::PostIncrement)
    .or(|| {
        parcel::left(parcel::join(
            whitespace_wrapped(postfix_expression()),
            whitespace_wrapped(expect_str("--")),
        ))
        .map(Box::new)
        .map(ExprNode::PostDecrement)
    })
    .or(postfix_expression)
}

fn new_post_increment_decrement_expression<'a>(
) -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::left(parcel::join(
        new_postfix_expression(),
        expect_tokentype(TokenType::PlusPlus),
    ))
    .map(Box::new)
    .map(ExprNode::PostIncrement)
    .or(|| {
        parcel::left(parcel::join(
            new_postfix_expression(),
            expect_tokentype(TokenType::MinusMinus),
        ))
        .map(Box::new)
        .map(ExprNode::PostDecrement)
    })
    .or(new_postfix_expression)
}

fn postfix_expression<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        identifier(),
        parcel::left(parcel::join(
            whitespace_wrapped(expect_character('[')).and_then(|_| expression()),
            whitespace_wrapped(expect_character(']')),
        )),
    )
    .map(|(id, expr)| ExprNode::Index(id, Box::new(expr)))
    .or(primary)
}

fn new_postfix_expression<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        new_identifier(),
        parcel::left(parcel::join(
            expect_tokentype(TokenType::LBracket).and_then(|_| new_expression()),
            expect_tokentype(TokenType::RBracket),
        )),
    )
    .map(|(id, expr)| ExprNode::Index(id, Box::new(expr)))
    .or(new_primary)
}

fn primary<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    number()
        .map(ExprNode::Primary)
        .or(|| character_literal().map(ExprNode::Primary))
        .or(|| string_literal().map(ExprNode::Primary))
        .or(|| identifier().map(|id| ExprNode::Primary(Primary::Identifier(id))))
        .or(grouping)
}

fn new_primary<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    new_number()
        .map(ExprNode::Primary)
        .or(|| new_character_literal().map(ExprNode::Primary))
        .or(|| new_string_literal().map(ExprNode::Primary))
        .or(|| new_identifier().map(|id| ExprNode::Primary(Primary::Identifier(id))))
        .or(new_grouping)
}

fn grouping<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    whitespace_wrapped(expect_character('('))
        .and_then(|_| {
            parcel::left(parcel::join(
                expression(),
                whitespace_wrapped(expect_character(')')),
            ))
        })
        .map(|expr| grouping_expr!(expr))
}

fn new_grouping<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    expect_tokentype(TokenType::LParen)
        .and_then(|_| {
            parcel::left(parcel::join(
                new_expression(),
                expect_tokentype(TokenType::RParen),
            ))
        })
        .map(|expr| grouping_expr!(expr))
}

fn string_literal<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], Primary> {
    character_wrapped(
        '"',
        '"',
        parcel::zero_or_more(
            ascii_alphanumeric()
                .or(ascii_whitespace)
                .or(ascii_control)
                // escaped quote
                .or(|| expect_character('\\').and_then(|_| expect_character('\"')))
                .map(|c| c as u8),
        ),
    )
    .map(ast::Primary::Str)
}

fn new_string_literal<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Primary> {
    expect_tokentype(TokenType::StrLiteral)
        .map(|tok| match tok {
            // guaranteed due to above constraint
            Token::StrLiteral(lit) => lit,
            _ => "".to_string(),
        })
        .map(|lit| lit.into_bytes())
        .map(ast::Primary::Str)
}

fn character_literal<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], Primary> {
    character_wrapped('\'', '\'', ascii().map(|c| c as u8)).map(|num| Primary::Integer {
        sign: Signed::Signed,
        width: IntegerWidth::Eight,
        value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
    })
}

fn new_character_literal<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Primary> {
    expect_tokentype(TokenType::CharLiteral)
        .map(|tok| match tok {
            // guaranteed due to above constraint
            Token::CharLiteral(c) => c as u8,
            _ => 0,
        })
        .map(|num| Primary::Integer {
            sign: Signed::Signed,
            width: IntegerWidth::Eight,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        })
}

fn number<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], Primary> {
    parcel::one_of(vec![
        dec_i8().map(|num| Primary::Integer {
            sign: Signed::Signed,
            width: IntegerWidth::Eight,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        dec_u8().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::Eight,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        dec_i16().map(|num| Primary::Integer {
            sign: Signed::Signed,
            width: IntegerWidth::Sixteen,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        dec_u16().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::Sixteen,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        dec_i32().map(|num| Primary::Integer {
            sign: Signed::Signed,
            width: IntegerWidth::ThirtyTwo,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        dec_u32().map(|num| Primary::Integer {
            sign: Signed::Signed,
            width: IntegerWidth::ThirtyTwo,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        dec_i64().map(|num| Primary::Integer {
            sign: Signed::Signed,
            width: IntegerWidth::SixtyFour,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        dec_u64().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::SixtyFour,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
    ])
}

fn new_number<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Primary> {
    parcel::one_of(vec![
        new_dec_i8().map(|num| Primary::Integer {
            sign: Signed::Signed,
            width: IntegerWidth::Eight,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        new_dec_u8().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::Eight,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        new_dec_i16().map(|num| Primary::Integer {
            sign: Signed::Signed,
            width: IntegerWidth::Sixteen,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        new_dec_u16().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::Sixteen,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        new_dec_i32().map(|num| Primary::Integer {
            sign: Signed::Signed,
            width: IntegerWidth::ThirtyTwo,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        new_dec_u32().map(|num| Primary::Integer {
            sign: Signed::Signed,
            width: IntegerWidth::ThirtyTwo,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        new_dec_i64().map(|num| Primary::Integer {
            sign: Signed::Signed,
            width: IntegerWidth::SixtyFour,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        new_dec_u64().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::SixtyFour,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
    ])
}

fn unsigned_number<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], Primary> {
    parcel::one_of(vec![
        dec_u8().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::Eight,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        dec_u16().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::Sixteen,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        dec_u32().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::ThirtyTwo,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        dec_u64().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::SixtyFour,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
    ])
}

fn new_unsigned_number<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Primary> {
    parcel::one_of(vec![
        new_dec_u8().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::Eight,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        new_dec_u16().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::Sixteen,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        new_dec_u32().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::ThirtyTwo,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
        new_dec_u64().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::SixtyFour,
            value: crate::util::pad_to_64bit_array(num.to_le_bytes()),
        }),
    ])
}

fn identifier<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], String> {
    parcel::one_or_more(ascii_alphanumeric().or(|| expect_character('_')))
        .map(|chars| chars.into_iter().collect::<String>())
        // guarantee the identifier is not a keyword.
        .predicate(|str| !RESERVED_KEYWORDS.contains(&str.as_str()))
}

fn new_identifier<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], String> {
    expect_tokentype(TokenType::Identifier).map(|t| {
        match t {
            Token::Identifier(id) => id,
            // safe unpack due to expect_tokentype constraint
            _ => unreachable!(),
        }
    })
}

fn type_declarator<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], Type> {
    whitespace_wrapped(
        parcel::join(
            type_specifier(),
            whitespace_wrapped(expect_character('*').one_or_more()),
        )
        .map(|(ty, pointer_depth)| {
            let nested_pointers = pointer_depth.len() - 1;
            (0..nested_pointers)
                .into_iter()
                .fold(Type::Pointer(Box::new(ty)), |acc, _| {
                    Type::Pointer(Box::new(acc))
                })
        }),
    )
    .or(type_specifier)
}

fn new_type_declarator<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Type> {
    parcel::join(
        new_type_specifier(),
        expect_tokentype(TokenType::Star).one_or_more(),
    )
    .map(|(ty, pointer_depth)| {
        let nested_pointers = pointer_depth.len() - 1;
        (0..nested_pointers)
            .into_iter()
            .fold(Type::Pointer(Box::new(ty)), |acc, _| {
                Type::Pointer(Box::new(acc))
            })
    })
    .or(new_type_specifier)
}

fn type_specifier<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], Type> {
    parcel::join(
        whitespace_wrapped(parcel::one_of(vec![
            expect_str("signed").map(|_| Signed::Signed),
            expect_str("unsigned").map(|_| Signed::Unsigned),
        ]))
        .optional(),
        whitespace_wrapped(parcel::one_of(vec![
            //
            // long parser
            //
            parcel::one_of(vec![
                // long long int
                whitespace_wrapped(expect_str("long"))
                    .and_then(|_| whitespace_wrapped(expect_str("long")))
                    .and_then(|_| whitespace_wrapped(expect_str("int"))),
                // long long
                whitespace_wrapped(expect_str("long"))
                    .and_then(|_| whitespace_wrapped(expect_str("long"))),
                // long int
                whitespace_wrapped(expect_str("long"))
                    .and_then(|_| whitespace_wrapped(expect_str("int"))),
                // long
                parcel::BoxedParser::new(expect_str("long")),
            ])
            .map(|_| Type::Integer(Signed::Signed, IntegerWidth::SixtyFour)),
            //
            // int parser
            //
            expect_str("int").map(|_| Type::Integer(Signed::Signed, IntegerWidth::ThirtyTwo)),
            //
            // short parser
            //
            parcel::one_of(vec![
                // short int
                whitespace_wrapped(expect_str("short"))
                    .and_then(|_| whitespace_wrapped(expect_str("int"))),
                // short
                parcel::BoxedParser::new(expect_str("short")),
            ])
            .map(|_| Type::Integer(Signed::Signed, IntegerWidth::Sixteen)),
            //
            // char parser
            //
            expect_str("char").map(|_| Type::Integer(Signed::Signed, IntegerWidth::Eight)),
            //
            // void parser
            //
            expect_str("void").map(|_| Type::Void),
        ])),
    )
    .map(|(sign, ty)| match (sign, ty) {
        (Some(sign), Type::Integer(_, width)) => Type::Integer(sign, width),
        (_, ty) => ty,
    })
}

fn new_type_specifier<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Type> {
    parcel::join(
        parcel::one_of(vec![
            expect_tokentype(TokenType::Signed).map(|_| Signed::Signed),
            expect_tokentype(TokenType::Unsigned).map(|_| Signed::Unsigned),
        ])
        .optional(),
        parcel::one_of(vec![
            //
            // long parser
            //
            parcel::one_of(vec![
                // long long int
                expect_tokentype(TokenType::Long)
                    .and_then(|_| expect_tokentype(TokenType::Long))
                    .and_then(|_| expect_tokentype(TokenType::Int)),
                // long long
                expect_tokentype(TokenType::Long).and_then(|_| expect_tokentype(TokenType::Long)),
                // long int
                expect_tokentype(TokenType::Long).and_then(|_| expect_tokentype(TokenType::Int)),
                // long
                parcel::BoxedParser::new(expect_tokentype(TokenType::Long)),
            ])
            .map(|_| Type::Integer(Signed::Signed, IntegerWidth::SixtyFour)),
            //
            // int parser
            //
            expect_tokentype(TokenType::Int)
                .map(|_| Type::Integer(Signed::Signed, IntegerWidth::ThirtyTwo)),
            //
            // short parser
            //
            parcel::one_of(vec![
                // short int
                expect_tokentype(TokenType::Short).and_then(|_| expect_tokentype(TokenType::Int)),
                // short
                parcel::BoxedParser::new(expect_tokentype(TokenType::Short)),
            ])
            .map(|_| Type::Integer(Signed::Signed, IntegerWidth::Sixteen)),
            //
            // char parser
            //
            expect_tokentype(TokenType::Char)
                .map(|_| Type::Integer(Signed::Signed, IntegerWidth::Eight)),
            //
            // void parser
            //
            expect_tokentype(TokenType::Void).map(|_| Type::Void),
        ]),
    )
    .map(|(sign, ty)| match (sign, ty) {
        (Some(sign), Type::Integer(_, width)) => Type::Integer(sign, width),
        (_, ty) => ty,
    })
}

macro_rules! new_numeric_type_parser {
    ($(unsigned, $parser_name:ident, $ret_type:ty,)*) => {
        $(
        #[allow(unused)]
        fn $parser_name<'a>() -> impl Parser<'a, &'a [(usize, Token)], $ret_type> {
            move |input: &'a [(usize, Token)]| {
                let preparsed_input = input;
                let res = expect_tokentype(TokenType::IntLiteral)
                    .map(|digit_token| {
                        if let Token::IntLiteral(i) = digit_token {
                           Some(i as $ret_type)
                        } else {
                           None
                        }
                    })
                    .parse(input);

                match res {
                    Ok(MatchStatus::Match {
                        span,
                        remainder,
                        inner: Some(u),
                    }) => Ok(MatchStatus::Match {
                        span,
                        remainder,
                        inner: u,
                    }),

                    Ok(MatchStatus::Match {
                        span: _,
                        remainder: _,
                        inner: None,
                    }) => Ok(MatchStatus::NoMatch(preparsed_input)),

                    Ok(MatchStatus::NoMatch(remainder)) => Ok(MatchStatus::NoMatch(remainder)),
                    Err(e) => Err(e),
                }
            }
        }
    )*
    };
    ($(signed, $parser_name:ident, $ret_type:ty,)*) => {
        $(
        #[allow(unused)]
        fn $parser_name<'a>() -> impl Parser<'a, &'a [(usize, Token)], $ret_type> {
            use std::convert::TryFrom;
            move |input: &'a [(usize, Token)]| {
                let preparsed_input = input;
                let res = parcel::join(expect_tokentype(TokenType::Minus).optional(), expect_tokentype(TokenType::IntLiteral))
                    .map(|(negative, digits)| {
                        match (negative, digits) {
                            (Some(_), Token::IntLiteral(i)) => Some(-(i as $ret_type)),
                            (None, Token::IntLiteral(i)) => Some(i as $ret_type),
                            _ => None
                        }
                    })
                    .parse(input);

                match res {
                    Ok(MatchStatus::Match {
                        span,
                        remainder,
                        inner: Some(u),
                    }) => Ok(MatchStatus::Match {
                        span,
                        remainder,
                        inner: u,
                    }),

                    Ok(MatchStatus::Match {
                        span: _,
                        remainder: _,
                        inner: None,
                    }) => Ok(MatchStatus::NoMatch(preparsed_input)),

                    Ok(MatchStatus::NoMatch(remainder)) => Ok(MatchStatus::NoMatch(remainder)),
                    Err(e) => Err(e),
                }
            }
        }
    )*
    };
}

macro_rules! numeric_type_parser {
    ($(unsigned, $parser_name:ident, $ret_type:ty,)*) => {
        $(
        #[allow(unused)]
        fn $parser_name<'a>() -> impl Parser<'a, &'a [(usize, char)], $ret_type> {
            move |input: &'a [(usize, char)]| {
                let preparsed_input = input;
                let res = parcel::one_or_more(digit(10))
                    .map(|digits| {
                        let vd: String = digits.into_iter().collect();
                        vd.parse::<$ret_type>()
                    })
                    .parse(input);

                match res {
                    Ok(MatchStatus::Match {
                        span,
                        remainder,
                        inner: Ok(u),
                    }) => Ok(MatchStatus::Match {
                        span,
                        remainder,
                        inner: u,
                    }),

                    Ok(MatchStatus::Match {
                        span: _,
                        remainder: _,
                        inner: Err(_),
                    }) => Ok(MatchStatus::NoMatch(preparsed_input)),

                    Ok(MatchStatus::NoMatch(remainder)) => Ok(MatchStatus::NoMatch(remainder)),
                    Err(e) => Err(e),
                }
            }
        }
    )*
    };
    ($(signed, $parser_name:ident, $ret_type:ty,)*) => {
        $(
        #[allow(unused)]
        fn $parser_name<'a>() -> impl Parser<'a, &'a [(usize, char)], $ret_type> {
            move |input: &'a [(usize, char)]| {
                let preparsed_input = input;
                let res = parcel::join(whitespace_wrapped(expect_character('-')).optional(), parcel::one_or_more(digit(10)))
                    .map(|(negative, digits)| {
                        let vd: String = if negative.is_some() {
                            format!("-{}", digits.into_iter().collect::<String>())
                        } else {
                            digits.into_iter().collect()
                        };
                        vd.parse::<$ret_type>()
                    })
                    .parse(input);

                match res {
                    Ok(MatchStatus::Match {
                        span,
                        remainder,
                        inner: Ok(u),
                    }) => Ok(MatchStatus::Match {
                        span,
                        remainder,
                        inner: u,
                    }),

                    Ok(MatchStatus::Match {
                        span: _,
                        remainder: _,
                        inner: Err(_),
                    }) => Ok(MatchStatus::NoMatch(preparsed_input)),

                    Ok(MatchStatus::NoMatch(remainder)) => Ok(MatchStatus::NoMatch(remainder)),
                    Err(e) => Err(e),
                }
            }
        }
    )*
    };
}

#[rustfmt::skip]
new_numeric_type_parser!(
    signed, new_dec_i8, i8,
    signed, new_dec_i16, i16,
    signed, new_dec_i32, i32,
    signed, new_dec_i64, i64,
);

#[rustfmt::skip]
new_numeric_type_parser!(
    unsigned, new_dec_u8, u8,
    unsigned, new_dec_u16, u16,
    unsigned, new_dec_u32, u32,
    unsigned, new_dec_u64, u64,
);

#[rustfmt::skip]
numeric_type_parser!(
    signed, dec_i8, i8,
    signed, dec_i16, i16,
    signed, dec_i32, i32,
    signed, dec_i64, i64,
);

#[rustfmt::skip]
numeric_type_parser!(
    unsigned, dec_u8, u8,
    unsigned, dec_u16, u16,
    unsigned, dec_u32, u32,
    unsigned, dec_u64, u64,
);

fn ascii<'a>() -> impl Parser<'a, &'a [(usize, char)], char> {
    parcel::right(parcel::join(
        expect_character('\\'),
        expect_character('\\')
            .map(|_| '\\')
            .or(|| expect_character('\'').map(|_| '\''))
            .or(|| expect_character('"').map(|_| '"')),
    ))
    .or(ascii_alphanumeric)
    .or(ascii_whitespace)
    .or(ascii_control)
    .or(|| any_character().predicate(|c| c.is_ascii()))
}

fn ascii_whitespace<'a>() -> impl Parser<'a, &'a [(usize, char)], char> {
    parcel::right(parcel::join(
        expect_character('\\'),
        expect_character('n')
            .map(|_| '\n')
            .or(|| expect_character('t').map(|_| '\t')),
    ))
    .or(any_character)
    .predicate(|c| c.is_ascii_whitespace())
}

fn ascii_alphanumeric<'a>() -> impl Parser<'a, &'a [(usize, char)], char> {
    any_character().predicate(|c| c.is_ascii_alphanumeric())
}

fn ascii_control<'a>() -> impl Parser<'a, &'a [(usize, char)], char> {
    parcel::right(parcel::join(
        expect_character('\\'),
        expect_character('r')
            .map(|_| '\r')
            .or(|| expect_character('0').map(|_| '\0')),
    ))
    .or(|| any_character().predicate(|c| c.is_ascii_control()))
}

fn whitespace_wrapped<'a, P, B>(parser: P) -> impl Parser<'a, &'a [(usize, char)], B>
where
    B: 'a,
    P: Parser<'a, &'a [(usize, char)], B> + 'a,
{
    parcel::right(parcel::join(
        parcel::zero_or_more(whitespace()),
        parcel::left(parcel::join(parser, parcel::zero_or_more(whitespace()))),
    ))
}

fn character_wrapped<'a, P, B>(
    prefix: char,
    suffix: char,
    parser: P,
) -> impl Parser<'a, &'a [(usize, char)], B>
where
    B: 'a,
    P: Parser<'a, &'a [(usize, char)], B> + 'a,
{
    parcel::right(parcel::join(
        whitespace_wrapped(expect_character(prefix)),
        parcel::left(parcel::join(
            parser,
            whitespace_wrapped(expect_character(suffix)),
        )),
    ))
}

fn tokentype_wrapped<'a, P, B>(
    prefix: TokenType,
    suffix: TokenType,
    parser: P,
) -> impl Parser<'a, &'a [(usize, Token)], B>
where
    B: 'a,
    P: Parser<'a, &'a [(usize, Token)], B> + 'a,
{
    parcel::right(parcel::join(
        expect_tokentype(prefix),
        parcel::left(parcel::join(parser, expect_tokentype(suffix))),
    ))
}

pub fn expect_tokentype<'a>(expected: TokenType) -> impl Parser<'a, &'a [(usize, Token)], Token> {
    move |input: &'a [(usize, Token)]| match input.get(0) {
        Some(&(pos, ref next)) if next.to_token_type() == expected => Ok(MatchStatus::Match {
            span: pos..pos + 1,
            remainder: &input[1..],
            inner: next.clone(),
        }),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

fn unzip<A, B>(pair: Vec<(A, B)>) -> (Vec<A>, Vec<B>) {
    pair.into_iter().unzip()
}
