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
pub fn parse(input: &[char]) -> Result<ExprNode, ParseErr> {
    expression()
        .parse(input)
        .map_err(ParseErr::UnexpectedToken)
        .and_then(|ms| match ms {
            MatchStatus::Match((_, en)) => Ok(en),
            MatchStatus::NoMatch(_) => {
                Err(ParseErr::Unspecified("not a valid expression".to_string()))
            }
        })
}

fn expression<'a>() -> impl parcel::Parser<'a, &'a [char], ExprNode> {
    addition()
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum AdditionExprOp {
    Plus,
    Minus,
}

#[allow(clippy::redundant_closure)]
fn addition<'a>() -> impl parcel::Parser<'a, &'a [char], ExprNode> {
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
}

#[allow(clippy::redundant_closure)]
fn multiplication<'a>() -> impl parcel::Parser<'a, &'a [char], ExprNode> {
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
                MultiplicationExprOp::Star => {
                    ExprNode::Multiplication(Box::new(lhs), Box::new(rhs))
                }
                MultiplicationExprOp::Slash => ExprNode::Division(Box::new(lhs), Box::new(rhs)),
            })
    })
    .or(|| primary())
}

#[allow(clippy::redundant_closure)]
fn primary<'a>() -> impl parcel::Parser<'a, &'a [char], ExprNode> {
    number().map(|num| ExprNode::Primary(Primary::Uint8(num)))
}

#[allow(clippy::redundant_closure)]
fn number<'a>() -> impl parcel::Parser<'a, &'a [char], Uint8> {
    dec_u8().map(|num| Uint8(num))
}

fn dec_u8<'a>() -> impl Parser<'a, &'a [char], u8> {
    move |input: &'a [char]| {
        let preparsed_input = input;
        let res = parcel::one_or_more(digit(10))
            .map(|digits| {
                let vd: String = digits.into_iter().collect();
                u8::from_str_radix(&vd, 10)
            })
            .parse(input);

        match res {
            Ok(MatchStatus::Match((rem, Ok(u)))) => Ok(MatchStatus::Match((rem, u))),
            Ok(MatchStatus::Match((_, Err(_)))) => Ok(MatchStatus::NoMatch(preparsed_input)),
            Ok(MatchStatus::NoMatch(rem)) => Ok(MatchStatus::NoMatch(rem)),
            Err(e) => Err(e),
        }
    }
}

fn whitespace_wrapped<'a, P, B>(parser: P) -> impl Parser<'a, &'a [char], B>
where
    B: 'a,
    P: Parser<'a, &'a [char], B> + 'a,
{
    parcel::right(parcel::join(
        parcel::zero_or_more(whitespace()),
        parcel::left(parcel::join(parser, parcel::zero_or_more(whitespace()))),
    ))
}

fn unzip<A, B>(pair: Vec<(A, B)>) -> (Vec<A>, Vec<B>) {
    pair.into_iter().unzip()
}
#[cfg(test)]
mod tests {
    macro_rules! term_expr {
        ($lhs:expr, '+', $rhs:expr) => {
            $crate::ast::ExprNode::Addition(Box::new($lhs), Box::new($rhs))
        };
        ($lhs:expr, '-', $rhs:expr) => {
            $crate::ast::ExprNode::Subtraction(Box::new($lhs), Box::new($rhs))
        };
    }

    macro_rules! factor_expr {
        ($lhs:expr, '*', $rhs:expr) => {
            $crate::ast::ExprNode::Multiplication(Box::new($lhs), Box::new($rhs))
        };
        ($lhs:expr, '/', $rhs:expr) => {
            $crate::ast::ExprNode::Division(Box::new($lhs), Box::new($rhs))
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
        let input: Vec<char> = "13 - 6 + 4 * 5 + 8 / 3".chars().collect();

        assert_eq!(
            Ok(term_expr!(
                term_expr!(
                    term_expr!(primary_expr!(13), '-', primary_expr!(6)),
                    '+',
                    factor_expr!(primary_expr!(4), '*', primary_expr!(5))
                ),
                '+',
                factor_expr!(primary_expr!(8), '/', primary_expr!(3))
            )),
            crate::parser::parse(&input)
        )
    }
}
