use parcel::parsers::character::*;
use parcel::prelude::v1::*;

pub use crate::stage::ast::Type;
use crate::stage::ast::{IntegerWidth, Signed};

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
            Primary::Str(_) => panic!("cannot use string literals as size specifier"),
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
    .map(|(lhs, rhs)| assignment_expr!(lhs, '=', rhs))
    .or(equality)
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

#[derive(Debug, Clone, Copy, PartialEq)]
enum RelationalExprOp {
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

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
        .or(|| {
            whitespace_wrapped(expect_character('-'))
                .and_then(|_| prefix_expression())
                .map(Box::new)
                .map(ExprNode::Negate)
        })
        .or(|| {
            whitespace_wrapped(expect_character('!'))
                .and_then(|_| prefix_expression())
                .map(Box::new)
                .map(ExprNode::Not)
        })
        .or(postfix_expression)
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

fn primary<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    identifier()
        .map(|id| ExprNode::Primary(Primary::Identifier(id)))
        .or(|| string_literal().map(ExprNode::Primary))
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
        .map(|expr| grouping_expr!(expr))
}

fn string_literal<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], Primary> {
    character_wrapped(
        '"',
        '"',
        parcel::zero_or_more(alphabetic().or(|| digit(10))),
    )
    .map(|chars| ast::Primary::Str(chars.into_iter().map(|c| c as u8).collect::<Vec<u8>>()))
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

macro_rules! numeric_type_parser {
    ($($parser_name:ident, $ret_type:ty,)*) => {
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
}

#[rustfmt::skip]
numeric_type_parser!(
    dec_i8, i8,
    dec_u8, u8,
    dec_i16, i16,
    dec_u16, u16,
    dec_i32, i32,
    dec_u32, u32,
    dec_i64, i64,
    dec_u64, u64,
);

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
                    term_expr!(primary_expr!(u8 13), '-', primary_expr!(u8 6)),
                    '+',
                    factor_expr!(primary_expr!(u8 4), '*', primary_expr!(u8 5))
                ),
                '+',
                factor_expr!(primary_expr!(u8 8), '/', primary_expr!(u8 3))
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
                    primary_expr!(u8 5)
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
                primary_expr!(u8 2),
                '*',
                grouping_expr!(term_expr!(primary_expr!(u8 3), '+', primary_expr!(u8 4)))
            ),
        )]));

        assert_eq!(&expected_result, &res);
    }

    #[test]
    fn should_parse_index_expressions_in_correct_precedence() {
        use parcel::Parser;

        let input: Vec<(usize, char)> = "{
    x[1];
}"
        .chars()
        .enumerate()
        .collect();
        let res = crate::parser::compound_statements()
            .parse(&input)
            .map(|ms| ms.unwrap());

        let expected_result = Ok(CompoundStmts::new(vec![StmtNode::Expression(
            ExprNode::Index("x".to_string(), Box::new(primary_expr!(u8 1))),
        )]));

        assert_eq!(&expected_result, &res);
    }
}
