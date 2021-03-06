use crate::ast::*;
use parcel::parsers::character::*;
use parcel::prelude::v1::*;

/// ParseErr represents a parser response that doesn't return a correct AstNode.
#[derive(Debug, Clone, PartialEq)]
pub enum ParseErr {
    UnexpectedToken(String),
    Unspecified(String),
}

/// parse expects a character slice as input and attempts to parse a valid
/// expression, returning a parse error if it is invalid.
pub fn parse(input: &[(usize, char)]) -> Result<CompoundStmts, ParseErr> {
    compound_statements()
        .parse(input)
        .map_err(ParseErr::UnexpectedToken)
        .and_then(|ms| match ms {
            MatchStatus::Match {
                span: _,
                remainder: _,
                inner,
            } => Ok(inner),
            MatchStatus::NoMatch(_) => {
                Err(ParseErr::Unspecified("not a valid expression".to_string()))
            }
        })
}

fn compound_statements<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], CompoundStmts> {
    parcel::right(parcel::join(
        whitespace_wrapped(expect_character('{')),
        parcel::left(parcel::join(
            parcel::zero_or_more(statement()),
            whitespace_wrapped(expect_character('}')),
        )),
    ))
    .map(|stmts| CompoundStmts::new(stmts))
}

fn statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    expression_statement()
        .or(|| declaration_statement())
        .or(|| assignment_statement())
        .or(|| if_statement())
}

fn declaration_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    parcel::left(parcel::join(
        parcel::right(parcel::join(
            whitespace_wrapped(expect_str("int")),
            whitespace_wrapped(identifier()),
        )),
        whitespace_wrapped(expect_character(';')),
    ))
    .map(DeclarationStmt::new)
    .map(StmtNode::Declaration)
}

fn assignment_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    parcel::left(parcel::join(
        parcel::join(
            whitespace_wrapped(identifier()),
            parcel::right(parcel::join(
                whitespace_wrapped(expect_character('=')),
                whitespace_wrapped(expression()),
            )),
        ),
        whitespace_wrapped(expect_character(';')),
    ))
    .map(|(ident, expr)| AssignmentStmt::new(ident, expr))
    .map(StmtNode::Assignment)
}

fn if_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    parcel::join(
        if_head(),
        parcel::optional(
            whitespace_wrapped(expect_str("else")).and_then(|_| compound_statements()),
        ),
    )
    .map(|((cond, cond_true), cond_false)| {
        IfStmt::new(cond, cond_true, cond_false.map(|stmts| stmts))
    })
    .map(StmtNode::If)
}

fn if_head<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], (ExprNode, CompoundStmts)> {
    whitespace_wrapped(expect_str("if"))
        .and_then(|_| parcel::join(parens_wrapped(expression()), compound_statements()))
}

fn expression_statement<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], StmtNode> {
    parcel::left(parcel::join(
        whitespace_wrapped(expression()),
        whitespace_wrapped(expect_character(';')),
    ))
    .map(ExpressionStmt::new)
    .map(StmtNode::Expression)
}

fn expression<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    equality()
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
                EqualityExprOp::Equal => {
                    ExprNode::Equal(EqualExprNode::new(Box::new(lhs), Box::new(rhs)))
                }
                EqualityExprOp::NotEqual => {
                    ExprNode::NotEqual(NotEqualExprNode::new(Box::new(lhs), Box::new(rhs)))
                }
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
                RelationalExprOp::LessThan => {
                    ExprNode::LessThan(LessThanExprNode::new(Box::new(lhs), Box::new(rhs)))
                }
                RelationalExprOp::LessEqual => {
                    ExprNode::LessEqual(LessEqualExprNode::new(Box::new(lhs), Box::new(rhs)))
                }
                RelationalExprOp::GreaterThan => {
                    ExprNode::GreaterThan(GreaterThanExprNode::new(Box::new(lhs), Box::new(rhs)))
                }
                RelationalExprOp::GreaterEqual => {
                    ExprNode::GreaterEqual(GreaterEqualExprNode::new(Box::new(lhs), Box::new(rhs)))
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
                AdditionExprOp::Plus => {
                    ExprNode::Addition(AdditionExprNode::new(Box::new(lhs), Box::new(rhs)))
                }
                AdditionExprOp::Minus => {
                    ExprNode::Subtraction(SubtractionExprNode::new(Box::new(lhs), Box::new(rhs)))
                }
            })
    })
    .or(|| multiplication())
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum MultiplicationExprOp {
    Star,
    Slash,
}

#[allow(clippy::redundant_closure)]
fn multiplication<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    parcel::join(
        primary(),
        parcel::zero_or_more(parcel::join(
            whitespace_wrapped(
                expect_character('*')
                    .map(|_| MultiplicationExprOp::Star)
                    .or(|| expect_character('/').map(|_| MultiplicationExprOp::Slash)),
            ),
            whitespace_wrapped(primary()),
        ))
        .map(unzip),
    )
    .map(|(first_expr, (operators, operands))| {
        operators
            .into_iter()
            .zip(operands.into_iter())
            .fold(first_expr, |lhs, (operator, rhs)| match operator {
                MultiplicationExprOp::Star => ExprNode::Multiplication(
                    MultiplicationExprNode::new(Box::new(lhs), Box::new(rhs)),
                ),
                MultiplicationExprOp::Slash => {
                    ExprNode::Division(DivisionExprNode::new(Box::new(lhs), Box::new(rhs)))
                }
            })
    })
    .or(|| primary())
}

#[allow(clippy::redundant_closure)]
fn primary<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], ExprNode> {
    identifier()
        .map(|id| ExprNode::Primary(Primary::Identifier(id)))
        .or(|| number().map(|num| ExprNode::Primary(Primary::Uint8(num))))
}

#[allow(clippy::redundant_closure)]
fn number<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], Uint8> {
    dec_u8().map(|num| Uint8(num))
}

#[allow(clippy::redundant_closure)]
fn identifier<'a>() -> impl parcel::Parser<'a, &'a [(usize, char)], String> {
    parcel::one_or_more(alphabetic()).map(|chars| chars.into_iter().collect())
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

fn parens_wrapped<'a, P, B>(parser: P) -> impl Parser<'a, &'a [(usize, char)], B>
where
    B: 'a,
    P: Parser<'a, &'a [(usize, char)], B> + 'a,
{
    parcel::right(parcel::join(
        whitespace_wrapped(expect_character('(')),
        parcel::left(parcel::join(
            parser,
            whitespace_wrapped(expect_character(')')),
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
            $crate::ast::ExprNode::Addition(AdditionExprNode::new(Box::new($lhs), Box::new($rhs)))
        };
        ($lhs:expr, '-', $rhs:expr) => {
            $crate::ast::ExprNode::Subtraction(SubtractionExprNode::new(
                Box::new($lhs),
                Box::new($rhs),
            ))
        };
    }

    macro_rules! factor_expr {
        ($lhs:expr, '*', $rhs:expr) => {
            $crate::ast::ExprNode::Multiplication(MultiplicationExprNode::new(
                Box::new($lhs),
                Box::new($rhs),
            ))
        };
        ($lhs:expr, '/', $rhs:expr) => {
            $crate::ast::ExprNode::Division(DivisionExprNode::new(Box::new($lhs), Box::new($rhs)))
        };
    }

    macro_rules! primary_expr {
        ($value:expr) => {
            $crate::ast::ExprNode::Primary(Primary::Uint8(Uint8($value)))
        };
    }

    use crate::ast::*;
    #[test]
    fn should_parse_complex_expression() {
        let input: Vec<(usize, char)> = "{ 13 - 6 + 4 * 5 + 8 / 3; }".chars().enumerate().collect();

        assert_eq!(
            Ok(CompoundStmts::new(vec![StmtNode::Expression(
                ExpressionStmt::new(term_expr!(
                    term_expr!(
                        term_expr!(primary_expr!(13), '-', primary_expr!(6)),
                        '+',
                        factor_expr!(primary_expr!(4), '*', primary_expr!(5))
                    ),
                    '+',
                    factor_expr!(primary_expr!(8), '/', primary_expr!(3))
                ))
            )])),
            crate::parser::parse(&input)
        )
    }
}
