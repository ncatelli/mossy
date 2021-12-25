use parcel::parsers::character::*;
use parcel::prelude::v1::*;

pub use crate::stage::ast::Type;
use crate::stage::ast::{IntegerWidth, Signed};

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
pub fn parse(input: &[(usize, char)]) -> Result<Program, ParseErr> {
    parcel::one_or_more(function_declaration().map(ast::GlobalDecls::Func).or(|| {
        semicolon_terminated_statement(declaration()).map(|stmt| {
            // safe to unpack due to declaration guarantee.
            if let ast::StmtNode::Declaration(decl) = stmt {
                ast::GlobalDecls::Var(decl)
            } else {
                unreachable!()
            }
        })
    }))
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
    .map(Program::new)
}

fn function_declaration<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], FunctionDeclaration> {
    parcel::join(
        parcel::join(type_declarator(), whitespace_wrapped(identifier())),
        parcel::right(parcel::join(
            expect_character('(').and_then(|_| whitespace_wrapped(expect_character(')'))),
            compound_statements(),
        )),
    )
    .map(|((ty, id), block)| FunctionDeclaration::new(id, ty, block))
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
            character_wrapped('[', ']', number()),
        )),
    )
    .map(|(ty, (id, size))| {
        let size = match size {
            Primary::Integer { value, .. } => value as usize,
            Primary::Identifier(_) => todo!(),
        };
        (ty, id, size)
    })
    .map(|(ty, id, size)| crate::stage::ast::Declaration::Array { ty, id, size })
    .map(StmtNode::Declaration)
    .or(|| {
        parcel::join(
            type_declarator(),
            whitespace_wrapped(parcel::one_or_more(parcel::left(parcel::join(
                identifier(),
                whitespace_wrapped(expect_character(',').optional()),
            )))),
        )
        .map(|(ty, ids)| crate::stage::ast::Declaration::Scalar(ty, ids))
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
                        preop_statement(),
                        parcel::join(
                            parcel::left(parcel::join(
                                expression(),
                                whitespace_wrapped(expect_str(";")),
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
    statement()
}

fn postop_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    statement()
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

fn assignment<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        whitespace_wrapped(equality()),
        whitespace_wrapped(expect_character('=')).and_then(|_| whitespace_wrapped(assignment())),
    )
    .map(|(lhs, rhs)| ExprNode::Assignment(Box::new(lhs), Box::new(rhs)))
    .or(equality)
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum EqualityExprOp {
    Equal,
    NotEqual,
}

#[allow(clippy::redundant_closure)]
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
                EqualityExprOp::Equal => ExprNode::Equal(Box::new(lhs), Box::new(rhs)),
                EqualityExprOp::NotEqual => ExprNode::NotEqual(Box::new(lhs), Box::new(rhs)),
            })
    })
    .or(|| relational())
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum RelationalExprOp {
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

#[allow(clippy::redundant_closure)]
fn relational<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        addition(),
        parcel::zero_or_more(parcel::join(
            whitespace_wrapped(
                expect_str("<=")
                    .map(|_| RelationalExprOp::LessEqual)
                    .or(|| expect_str(">=").map(|_| RelationalExprOp::GreaterEqual))
                    .or(|| expect_str("<").map(|_| RelationalExprOp::LessThan))
                    .or(|| expect_str(">").map(|_| RelationalExprOp::GreaterThan)),
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
    .or(|| addition())
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum AdditionExprOp {
    Plus,
    Minus,
}

#[allow(clippy::redundant_closure)]
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
                AdditionExprOp::Plus => ExprNode::Addition(Box::new(lhs), Box::new(rhs)),
                AdditionExprOp::Minus => ExprNode::Subtraction(Box::new(lhs), Box::new(rhs)),
            })
    })
    .or(|| multiplication())
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum MultiplicationExprOp {
    Star,
    Slash,
    Mod,
}

#[allow(clippy::redundant_closure)]
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
                    ExprNode::Multiplication(Box::new(lhs), Box::new(rhs))
                }
                MultiplicationExprOp::Slash => ExprNode::Division(Box::new(lhs), Box::new(rhs)),
                MultiplicationExprOp::Mod => ExprNode::Modulo(Box::new(lhs), Box::new(rhs)),
            })
    })
    .or(|| call())
}

fn call<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        identifier(),
        parcel::left(parcel::join(
            whitespace_wrapped(expect_character('(')).and_then(|_| expression().optional()),
            whitespace_wrapped(expect_character(')')),
        )),
    )
    .map(|(id, expr)| ExprNode::FunctionCall(id, expr.map(Box::new)))
    .or(prefix_expression)
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
        .or(primary)
}

fn primary<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    identifier()
        .map(|id| ExprNode::Primary(Primary::Identifier(id)))
        .or(|| number().map(ExprNode::Primary))
        .or(grouping)
}

fn grouping<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    whitespace_wrapped(expect_character('('))
        .and_then(|_| {
            parcel::left(parcel::join(
                expression(),
                whitespace_wrapped(expect_character(')')),
            ))
        })
        .map(|expr| ExprNode::Grouping(Box::new(expr)))
}

fn number<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], Primary> {
    parcel::one_of(vec![
        dec_u8().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::Eight,
            value: u64::from(num),
        }),
        dec_u32().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::ThirtyTwo,
            value: u64::from(num),
        }),
        dec_u64().map(|num| Primary::Integer {
            sign: Signed::Unsigned,
            width: IntegerWidth::SixtyFour,
            value: num,
        }),
    ])
}

fn identifier<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], String> {
    parcel::one_or_more(alphabetic()).map(|chars| chars.into_iter().collect())
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

fn type_specifier<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], Type> {
    whitespace_wrapped(parcel::one_of(vec![
        expect_str("long").map(|_| Type::Integer(Signed::Unsigned, IntegerWidth::SixtyFour)),
        expect_str("int").map(|_| Type::Integer(Signed::Unsigned, IntegerWidth::ThirtyTwo)),
        expect_str("short").map(|_| Type::Integer(Signed::Unsigned, IntegerWidth::Sixteen)),
        expect_str("char").map(|_| Type::Integer(Signed::Unsigned, IntegerWidth::Eight)),
        expect_str("void").map(|_| Type::Void),
    ]))
}

fn dec_u64<'a>() -> impl Parser<'a, &'a [(usize, char)], u64> {
    move |input: &'a [(usize, char)]| {
        let preparsed_input = input;
        let res = parcel::one_or_more(digit(10))
            .map(|digits| {
                let vd: String = digits.into_iter().collect();
                vd.parse::<u64>()
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

fn dec_u32<'a>() -> impl Parser<'a, &'a [(usize, char)], u32> {
    move |input: &'a [(usize, char)]| {
        let preparsed_input = input;
        let res = parcel::one_or_more(digit(10))
            .map(|digits| {
                let vd: String = digits.into_iter().collect();
                vd.parse::<u32>()
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

fn dec_u8<'a>() -> impl Parser<'a, &'a [(usize, char)], u8> {
    move |input: &'a [(usize, char)]| {
        let preparsed_input = input;
        let res = parcel::one_or_more(digit(10))
            .map(|digits| {
                let vd: String = digits.into_iter().collect();
                vd.parse::<u8>()
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

fn unzip<A, B>(pair: Vec<(A, B)>) -> (Vec<A>, Vec<B>) {
    pair.into_iter().unzip()
}
#[cfg(test)]
mod tests {
    macro_rules! term_expr {
        ($lhs:expr, '+', $rhs:expr) => {
            $crate::parser::ast::ExprNode::Addition(Box::new($lhs), Box::new($rhs))
        };
        ($lhs:expr, '-', $rhs:expr) => {
            $crate::parser::ast::ExprNode::Subtraction(Box::new($lhs), Box::new($rhs))
        };
        ($lhs:expr, '%', $rhs:expr) => {
            $crate::parser::ast::ExprNode::Modulo(Box::new($lhs), Box::new($rhs))
        };
    }

    macro_rules! factor_expr {
        ($lhs:expr, '*', $rhs:expr) => {
            $crate::parser::ast::ExprNode::Multiplication(Box::new($lhs), Box::new($rhs))
        };
        ($lhs:expr, '/', $rhs:expr) => {
            $crate::parser::ast::ExprNode::Division(Box::new($lhs), Box::new($rhs))
        };
    }

    macro_rules! primary_expr {
        ($value:expr) => {
            $crate::parser::ast::ExprNode::Primary(crate::parser::ast::Primary::Integer {
                sign: $crate::stage::ast::Signed::Unsigned,
                width: $crate::stage::ast::IntegerWidth::Eight,
                value: $value,
            })
        };
    }

    macro_rules! grouping_expr {
        ($value:expr) => {
            $crate::parser::ast::ExprNode::Grouping(Box::new($value))
        };
    }

    use crate::parser::ast::*;

    #[test]
    fn should_parse_complex_arithmetic_expression() {
        use parcel::Parser;

        let input: Vec<(usize, char)> = "{ 13 - 6 + 4 * 5 + 8 / 3; }".chars().enumerate().collect();
        let res = crate::parser::compound_statements()
            .parse(&input)
            .map(|ms| ms.unwrap());

        assert_eq!(
            Ok(CompoundStmts::new(vec![StmtNode::Expression(term_expr!(
                term_expr!(
                    term_expr!(primary_expr!(13), '-', primary_expr!(6)),
                    '+',
                    factor_expr!(primary_expr!(4), '*', primary_expr!(5))
                ),
                '+',
                factor_expr!(primary_expr!(8), '/', primary_expr!(3))
            ))])),
            res
        )
    }

    #[test]
    fn should_parse_a_keyword_from_a_dereferenced_identifier() {
        use parcel::Parser;

        let input: Vec<(usize, char)> = "{ return *x; }".chars().enumerate().collect();
        let res = crate::parser::compound_statements()
            .parse(&input)
            .map(|ms| ms.unwrap());

        let expected_result = Ok(CompoundStmts::new(vec![StmtNode::Return(Some(
            ExprNode::Deref(Box::new(ExprNode::Primary(Primary::Identifier(
                "x".to_string(),
            )))),
        ))]));

        assert_eq!(&expected_result, &res);

        let input_with_arbitrary_whitespace: Vec<(usize, char)> =
            "{ return *          \n\nx; }".chars().enumerate().collect();
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

        let input: Vec<(usize, char)> = "{ x = y = 5; }".chars().enumerate().collect();
        let res = crate::parser::compound_statements()
            .parse(&input)
            .map(|ms| ms.unwrap());

        let expected_result = Ok(CompoundStmts::new(vec![StmtNode::Expression(
            assignment_expr!(
                ExprNode::Primary(Primary::Identifier("x".to_string())),
                assignment_expr!(
                    ExprNode::Primary(Primary::Identifier("y".to_string())),
                    primary_expr!(5)
                )
            ),
        )]));

        assert_eq!(&expected_result, &res);
    }

    #[test]
    fn should_parse_grouping_expressions_in_correct_precedence() {
        use parcel::Parser;

        let input: Vec<(usize, char)> = "{
    2 * (3 + 4);
}"
        .chars()
        .enumerate()
        .collect();
        let res = crate::parser::compound_statements()
            .parse(&input)
            .map(|ms| ms.unwrap());

        let expected_result = Ok(CompoundStmts::new(vec![StmtNode::Expression(
            factor_expr!(
                primary_expr!(2),
                '*',
                grouping_expr!(term_expr!(primary_expr!(3), '+', primary_expr!(4)))
            ),
        )]));

        assert_eq!(&expected_result, &res);
    }
}
