use parcel::prelude::v1::*;

use crate::lexer::{Token, TokenType};

pub use crate::stage::type_check::ast::Type;
use crate::stage::type_check::{
    self,
    ast::{IntegerWidth, Signed},
};

#[macro_use]
pub mod ast;
use ast::*;

/// ParseErr represents a parser response that doesn't return a correct AstNode.
#[derive(Debug, Clone, PartialEq)]
pub enum ParseErr {
    UnexpectedToken(String),
    Unspecified(String),
}

/// parse expects a character slice as input and attempts to parse a valid
/// expression, returning a parse error if it is invalid.
pub fn parse(input: &[(usize, Token)]) -> Result<CompilationUnit, ParseErr> {
    parcel::one_or_more(
        function_definition()
            .map(ast::GlobalDecls::FuncDefinition)
            .or(|| {
                parcel::left(parcel::join(
                    function_prototype(),
                    expect_tokentype(TokenType::SemiColon),
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

fn function_prototype<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], FunctionProto> {
    parcel::join(
        parcel::join(type_declarator(), identifier()),
        expect_tokentype(TokenType::LParen).and_then(|_| {
            parcel::left(parcel::join(
                parcel::join(
                    parcel::zero_or_more(
                        parcel::join(
                            type_declarator(),
                            parcel::left(parcel::join(
                                identifier(),
                                expect_tokentype(TokenType::Comma),
                            )),
                        )
                        .map(|(ty, id)| ast::Parameter::new(id, ty)),
                    ),
                    parcel::join(type_declarator(), identifier())
                        .map(|(ty, id)| ast::Parameter::new(id, ty)),
                )
                .map(|(mut head, tail)| {
                    head.push(tail);
                    head
                })
                .or(|| {
                    parcel::zero_or_more(
                        parcel::join(type_declarator(), identifier())
                            .map(|(ty, id)| ast::Parameter::new(id, ty)),
                    )
                }),
                expect_tokentype(TokenType::RParen),
            ))
        }),
    )
    .map(|((ty, id), params)| FunctionProto::new(id, ty, params))
}

fn function_definition<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], FunctionDefinition> {
    parcel::join(function_prototype(), compound_statements())
        .map(|(proto, block)| FunctionDefinition::new(proto, block))
}

fn compound_statements<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], CompoundStmts> {
    tokentype_wrapped(
        TokenType::LBrace,
        TokenType::RBrace,
        parcel::zero_or_more(statement()),
    )
    .map(CompoundStmts::new)
}

fn statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], StmtNode> {
    semicolon_terminated_statement(declaration())
        .or(if_statement)
        .or(while_statement)
        .or(for_statement)
        .or(|| semicolon_terminated_statement(return_statement()))
        .or(|| semicolon_terminated_statement(expression().map(StmtNode::Expression)))
}

fn semicolon_terminated_statement<'a, P>(
    term: P,
) -> impl parcel::Parser<'a, &'a [(usize, Token)], StmtNode>
where
    P: parcel::Parser<'a, &'a [(usize, Token)], StmtNode> + 'a,
{
    parcel::left(parcel::join(term, expect_tokentype(TokenType::SemiColon)))
}

fn declaration<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], StmtNode> {
    parcel::join(
        type_declarator(),
        parcel::join(
            identifier(),
            tokentype_wrapped(TokenType::LBracket, TokenType::RBracket, unsigned_number()),
        ),
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
            parcel::one_or_more(parcel::left(parcel::join(
                identifier(),
                expect_tokentype(TokenType::Comma).optional(),
            ))),
        )
        .map(|(ty, ids)| type_check::ast::Declaration::Scalar(ty, ids))
        .map(StmtNode::Declaration)
    })
}

fn if_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], StmtNode> {
    parcel::join(
        if_head(),
        parcel::optional(expect_tokentype(TokenType::Else).and_then(|_| compound_statements())),
    )
    .map(|((cond, cond_true), cond_false)| StmtNode::If(cond, cond_true, cond_false))
}

fn if_head<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], (ExprNode, CompoundStmts)> {
    expect_tokentype(TokenType::If).and_then(|_| {
        parcel::join(
            tokentype_wrapped(TokenType::LParen, TokenType::RParen, expression()),
            compound_statements(),
        )
    })
}

fn while_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], StmtNode> {
    expect_tokentype(TokenType::While)
        .and_then(|_| {
            parcel::join(
                tokentype_wrapped(TokenType::LParen, TokenType::RParen, expression()),
                compound_statements(),
            )
        })
        .map(|(cond, block)| StmtNode::While(cond, block))
}

fn for_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], StmtNode> {
    expect_tokentype(TokenType::For)
        .and_then(|_| {
            parcel::join(
                tokentype_wrapped(
                    TokenType::LParen,
                    TokenType::RParen,
                    parcel::join(
                        parcel::left(parcel::join(
                            preop_statement(),
                            expect_tokentype(TokenType::SemiColon),
                        )),
                        parcel::join(
                            parcel::left(parcel::join(
                                expression(),
                                expect_tokentype(TokenType::SemiColon),
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

fn preop_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], StmtNode> {
    assignment().map(StmtNode::Expression)
}

fn postop_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], StmtNode> {
    expression().map(StmtNode::Expression)
}

fn return_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], StmtNode> {
    parcel::right(parcel::join(
        expect_tokentype(TokenType::Return),
        expression().optional(),
    ))
    .map(StmtNode::Return)
}

fn expression<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    assignment()
}

fn assignment<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        logical(),
        expect_tokentype(TokenType::Equal).and_then(|_| assignment()),
    )
    .map(|(lhs, rhs)| assignment_expr!(lhs, '=', rhs))
    .or(logical)
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum LogicalExprOp {
    Or,
    And,
}

fn logical<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        bitwise(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::PipePipe)
                .map(|_| LogicalExprOp::Or)
                .or(|| expect_tokentype(TokenType::AmpersandAmpersand).map(|_| LogicalExprOp::And)),
            bitwise(),
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

fn bitwise<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        equality(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::Pipe)
                .map(|_| BitwiseExprOp::Or)
                .or(|| expect_tokentype(TokenType::Carat).map(|_| BitwiseExprOp::Xor))
                .or(|| expect_tokentype(TokenType::Ampersand).map(|_| BitwiseExprOp::And)),
            equality(),
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

fn equality<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        relational(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::EqualEqual)
                .map(|_| EqualityExprOp::Equal)
                .or(|| expect_tokentype(TokenType::BangEqual).map(|_| EqualityExprOp::NotEqual)),
            relational(),
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

fn relational<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        bitwise_shift(),
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
            bitwise_shift(),
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

fn bitwise_shift<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        addition(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::LShift)
                .map(|_| BitwiseShiftExprOp::ShiftLeft)
                .or(|| expect_tokentype(TokenType::RShift).map(|_| BitwiseShiftExprOp::ShiftRight)),
            addition(),
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

fn addition<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        multiplication(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::Plus)
                .map(|_| AdditionExprOp::Plus)
                .or(|| expect_tokentype(TokenType::Minus).map(|_| AdditionExprOp::Minus)),
            multiplication(),
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

fn multiplication<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        call(),
        parcel::zero_or_more(parcel::join(
            expect_tokentype(TokenType::Star)
                .map(|_| MultiplicationExprOp::Star)
                .or(|| expect_tokentype(TokenType::Slash).map(|_| MultiplicationExprOp::Slash))
                .or(|| expect_tokentype(TokenType::PercentSign).map(|_| MultiplicationExprOp::Mod)),
            call(),
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

fn call<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        identifier(),
        expect_tokentype(TokenType::LParen).and_then(|_| {
            parcel::left(parcel::join(
                parcel::join(
                    parcel::zero_or_more(parcel::left(parcel::join(
                        expression(),
                        expect_tokentype(TokenType::Comma),
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
                expect_tokentype(TokenType::RParen),
            ))
        }),
    )
    .map(|(id, exprs)| ExprNode::FunctionCall(id, exprs))
    .or(prefix_expression)
}

fn prefix_expression<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    expect_tokentype(TokenType::Star)
        .and_then(|_| prefix_expression())
        .map(Box::new)
        .map(ExprNode::Deref)
        .or(|| {
            expect_tokentype(TokenType::Ampersand)
                .and_then(|_| identifier())
                .map(ExprNode::Ref)
        })
        .or(|| {
            expect_tokentype(TokenType::PlusPlus)
                .and_then(|_| prefix_expression())
                .map(Box::new)
                .map(ExprNode::PreIncrement)
        })
        .or(|| {
            expect_tokentype(TokenType::MinusMinus)
                .and_then(|_| prefix_expression())
                .map(Box::new)
                .map(ExprNode::PreDecrement)
        })
        // unary logical not
        .or(|| {
            expect_tokentype(TokenType::Bang)
                .and_then(|_| prefix_expression())
                .map(Box::new)
                .map(ExprNode::LogicalNot)
        })
        // unary negate
        .or(|| {
            expect_tokentype(TokenType::Minus)
                .and_then(|_| prefix_expression())
                // prevent negate from eating `-` on integer literals.
                .predicate(|e| !matches!(e, ExprNode::Primary(Primary::Integer { .. })))
                .map(Box::new)
                .map(ExprNode::Negate)
        })
        // unary inverse
        .or(|| {
            expect_tokentype(TokenType::Tilde)
                .and_then(|_| prefix_expression())
                .map(Box::new)
                .map(ExprNode::Invert)
        })
        .or(post_increment_decrement_expression)
}

fn post_increment_decrement_expression<'a>(
) -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::left(parcel::join(
        postfix_expression(),
        expect_tokentype(TokenType::PlusPlus),
    ))
    .map(Box::new)
    .map(ExprNode::PostIncrement)
    .or(|| {
        parcel::left(parcel::join(
            postfix_expression(),
            expect_tokentype(TokenType::MinusMinus),
        ))
        .map(Box::new)
        .map(ExprNode::PostDecrement)
    })
    .or(postfix_expression)
}

fn postfix_expression<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    parcel::join(
        identifier(),
        parcel::left(parcel::join(
            expect_tokentype(TokenType::LBracket).and_then(|_| expression()),
            expect_tokentype(TokenType::RBracket),
        )),
    )
    .map(|(id, expr)| ExprNode::Index(id, Box::new(expr)))
    .or(primary)
}

fn primary<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    number()
        .map(ExprNode::Primary)
        .or(|| character_literal().map(ExprNode::Primary))
        .or(|| string_literal().map(ExprNode::Primary))
        .or(|| identifier().map(|id| ExprNode::Primary(Primary::Identifier(id))))
        .or(grouping)
}

fn grouping<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], ExprNode> {
    expect_tokentype(TokenType::LParen)
        .and_then(|_| {
            parcel::left(parcel::join(
                expression(),
                expect_tokentype(TokenType::RParen),
            ))
        })
        .map(|expr| grouping_expr!(expr))
}

fn string_literal<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Primary> {
    expect_tokentype(TokenType::StrLiteral)
        .map(|tok| match tok {
            // guaranteed due to above constraint
            Token::StrLiteral(lit) => lit,
            _ => "".to_string(),
        })
        .map(|lit| lit.into_bytes())
        .map(ast::Primary::Str)
}

fn character_literal<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Primary> {
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

fn number<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Primary> {
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

fn unsigned_number<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Primary> {
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

fn identifier<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], String> {
    expect_tokentype(TokenType::Identifier).map(|t| {
        match t {
            Token::Identifier(id) => id,
            // safe unpack due to expect_tokentype constraint
            _ => unreachable!(),
        }
    })
}

fn type_declarator<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Type> {
    parcel::join(
        type_specifier(),
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
    .or(type_specifier)
}

fn type_specifier<'a>() -> impl parcel::Parser<'a, &'a [(usize, Token)], Type> {
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

macro_rules! numeric_type_parser {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_parse_complex_arithmetic_expression() {
        use crate::lexer::Token;
        use parcel::Parser;

        // { 13 - 6 + 4 * 5 + 8 / 3; }
        let input: Vec<(usize, Token)> = vec![
            Token::LBrace,
            Token::IntLiteral(13),
            Token::Minus,
            Token::IntLiteral(6),
            Token::Plus,
            Token::IntLiteral(4),
            Token::Star,
            Token::IntLiteral(5),
            Token::Plus,
            Token::IntLiteral(8),
            Token::Slash,
            Token::IntLiteral(3),
            Token::SemiColon,
            Token::RBrace,
        ]
        .into_iter()
        .enumerate()
        .collect();
        let res = compound_statements().parse(&input).map(|ms| ms.unwrap());

        assert_eq!(
            Ok(CompoundStmts::new(vec![StmtNode::Expression(term_expr!(
                term_expr!(
                    term_expr!(primary_expr!(i8 13), '-', primary_expr!(i8 6)),
                    '+',
                    factor_expr!(primary_expr!(i8 4), '*', primary_expr!(i8 5))
                ),
                '+',
                factor_expr!(primary_expr!(i8 8), '/', primary_expr!(i8 3))
            ))])),
            res
        )
    }

    #[test]
    fn should_parse_unary_expressions() {
        use parcel::Parser;

        // { !1 + -2; }
        let input: Vec<(usize, Token)> = vec![
            Token::LBrace,
            Token::Bang,
            Token::IntLiteral(1),
            Token::Plus,
            Token::Minus,
            Token::IntLiteral(2),
            Token::SemiColon,
            Token::RBrace,
        ]
        .into_iter()
        .enumerate()
        .collect();
        let res = compound_statements().parse(&input).map(|ms| ms.unwrap());

        assert_eq!(
            Ok(CompoundStmts::new(vec![StmtNode::Expression(term_expr!(
                ExprNode::LogicalNot(Box::new(primary_expr!(i8 1))),
                '+',
                primary_expr!(i8 - 2)
            ),)])),
            res
        )
    }

    #[test]
    fn should_parse_a_keyword_from_a_dereferenced_identifier() {
        use parcel::Parser;

        // { return *x; }
        let input: Vec<(usize, Token)> = vec![
            Token::LBrace,
            Token::Return,
            Token::Star,
            Token::Identifier("x".to_string()),
            Token::SemiColon,
            Token::RBrace,
        ]
        .into_iter()
        .enumerate()
        .collect();
        let res = compound_statements().parse(&input).map(|ms| ms.unwrap());

        let expected_result = Ok(CompoundStmts::new(vec![StmtNode::Return(Some(
            ExprNode::Deref(Box::new(ExprNode::Primary(Primary::Identifier(
                "x".to_string(),
            )))),
        ))]));

        assert_eq!(&expected_result, &res);

        // { return *          \n\nx; }
        let input_with_arbitrary_whitespace: Vec<(usize, Token)> = vec![
            Token::LBrace,
            Token::Return,
            Token::Star,
            Token::Identifier("x".to_string()),
            Token::SemiColon,
            Token::RBrace,
        ]
        .into_iter()
        .enumerate()
        .collect();
        let res = crate::parser::compound_statements()
            .parse(&input_with_arbitrary_whitespace)
            .map(|ms| ms.unwrap());

        assert_eq!(&expected_result, &res)
    }

    macro_rules! assignment_expr {
        ($lhs:expr, $rhs:expr) => {
            ExprNode::Assignment(Box::new($lhs), Box::new($rhs))
        };
    }

    #[test]
    fn should_parse_multiple_nested_assignment_expressions() {
        use parcel::Parser;

        // { x = y = 5; }
        let input: Vec<(usize, Token)> = vec![
            Token::LBrace,
            Token::Identifier("x".to_string()),
            Token::Equal,
            Token::Identifier("y".to_string()),
            Token::Equal,
            Token::IntLiteral(5),
            Token::SemiColon,
            Token::RBrace,
        ]
        .into_iter()
        .enumerate()
        .collect();
        let res = compound_statements().parse(&input).map(|ms| ms.unwrap());

        let expected_result = Ok(CompoundStmts::new(vec![StmtNode::Expression(
            assignment_expr!(
                ExprNode::Primary(Primary::Identifier("x".to_string())),
                assignment_expr!(
                    ExprNode::Primary(Primary::Identifier("y".to_string())),
                    primary_expr!(i8 5)
                )
            ),
        )]));

        assert_eq!(&expected_result, &res);
    }

    #[test]
    fn should_parse_grouping_expressions_in_correct_precedence() {
        use parcel::Parser;

        // { 2 * (3 + 4); }
        let input: Vec<(usize, Token)> = vec![
            Token::LBrace,
            Token::IntLiteral(2),
            Token::Star,
            Token::LParen,
            Token::IntLiteral(3),
            Token::Plus,
            Token::IntLiteral(4),
            Token::RParen,
            Token::SemiColon,
            Token::RBrace,
        ]
        .into_iter()
        .enumerate()
        .collect();
        let res = compound_statements().parse(&input).map(|ms| ms.unwrap());

        let expected_result = Ok(CompoundStmts::new(vec![StmtNode::Expression(
            factor_expr!(
                primary_expr!(i8 2),
                '*',
                grouping_expr!(term_expr!(primary_expr!(i8 3), '+', primary_expr!(i8 4)))
            ),
        )]));

        assert_eq!(&expected_result, &res);
    }

    #[test]
    fn should_parse_string_literals() {
        use parcel::Parser;

        // { "hello\n\t\"world\""; }
        let input: Vec<(usize, Token)> = vec![
            Token::LBrace,
            Token::StrLiteral("hello\n\t\"world\"".to_string()),
            Token::SemiColon,
            Token::RBrace,
        ]
        .into_iter()
        .enumerate()
        .collect();
        let res = compound_statements().parse(&input).map(|ms| ms.unwrap());

        let expected_result = Ok(CompoundStmts::new(vec![StmtNode::Expression(
            primary_expr!(str "hello\n\t\"world\""),
        )]));

        assert_eq!(&expected_result, &res);
    }

    #[test]
    fn should_parse_character_literals() {
        use parcel::Parser;

        // { \'a\'; }
        let input: Vec<(usize, Token)> = vec![
            Token::LBrace,
            Token::CharLiteral('a'),
            Token::SemiColon,
            Token::RBrace,
        ]
        .into_iter()
        .enumerate()
        .collect();
        let res = compound_statements().parse(&input).map(|ms| ms.unwrap());

        let expected_result = Ok(CompoundStmts::new(vec![StmtNode::Expression(
            primary_expr!(i8 97),
        )]));

        assert_eq!(&expected_result, &res);
    }

    #[test]
    fn should_parse_index_expressions_in_correct_precedence() {
        use parcel::Parser;

        // "{ x[1]; }"
        let input: Vec<(usize, Token)> = vec![
            Token::LBrace,
            Token::Identifier("x".to_string()),
            Token::LBracket,
            Token::IntLiteral(1),
            Token::RBracket,
            Token::SemiColon,
            Token::RBrace,
        ]
        .into_iter()
        .enumerate()
        .collect();
        let res = compound_statements().parse(&input).map(|ms| ms.unwrap());

        let expected_result = Ok(CompoundStmts::new(vec![StmtNode::Expression(
            ExprNode::Index("x".to_string(), Box::new(primary_expr!(i8 1))),
        )]));

        assert_eq!(&expected_result, &res);
    }

    #[test]
    fn should_parse_for_statement() {
        use parcel::Parser;

        // { for (i=0; i<5; i++) { i; } }
        let input: Vec<(usize, Token)> = vec![
            Token::LBrace,
            Token::For,
            Token::LParen,
            Token::Identifier("i".to_string()),
            Token::Equal,
            Token::IntLiteral(0),
            Token::SemiColon,
            Token::Identifier("i".to_string()),
            Token::LessThan,
            Token::IntLiteral(5),
            Token::SemiColon,
            Token::Identifier("i".to_string()),
            Token::PlusPlus,
            Token::RParen,
            Token::LBrace,
            Token::Identifier("i".to_string()),
            Token::SemiColon,
            Token::RBrace,
            Token::RBrace,
        ]
        .into_iter()
        .enumerate()
        .collect();
        let res = compound_statements().parse(&input).map(|ms| ms.unwrap());

        let expected_result = Ok(CompoundStmts::new(vec![StmtNode::For(
            Box::new(StmtNode::Expression(assignment_expr!(
                ExprNode::Primary(Primary::Identifier("i".to_string())),
                primary_expr!(i8 0)
            ))),
            ExprNode::LessThan(
                Box::new(ExprNode::Primary(Primary::Identifier("i".to_string()))),
                Box::new(primary_expr!(i8 5)),
            ),
            Box::new(StmtNode::Expression(ExprNode::PostIncrement(Box::new(
                ExprNode::Primary(Primary::Identifier("i".to_string())),
            )))),
            CompoundStmts::new(vec![StmtNode::Expression(ExprNode::Primary(
                Primary::Identifier("i".to_string()),
            ))]),
        )]));

        assert_eq!(&expected_result, &res);
    }

    #[test]
    fn should_fail_to_parse_keyword_as_identifier() {
        use parcel::Parser;

        // { return auto; }
        let input: Vec<(usize, Token)> = vec![
            Token::LBrace,
            Token::Return,
            Token::Auto,
            Token::SemiColon,
            Token::RBrace,
        ]
        .into_iter()
        .enumerate()
        .collect();
        let res = compound_statements()
            .parse(&input)
            .ok()
            .and_then(|ms| match ms {
                parcel::MatchStatus::Match { .. } => None,
                parcel::MatchStatus::NoMatch(_) => Some(()),
            });

        assert!(res.is_some());
    }
}
