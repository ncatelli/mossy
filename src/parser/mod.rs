use crate::ast::*;
use parcel::parsers::character::*;
use parcel::prelude::v1::*;
use parcel::*;

pub fn expression<'a>() -> impl parcel::Parser<'a, &'a [char], ExprNode> {
    addition()
}

#[allow(clippy::redundant_closure)]
fn addition<'a>() -> impl parcel::Parser<'a, &'a [char], ExprNode> {
    join(
        multiplication(),
        right(join(
            parcel::zero_or_more(non_newline_whitespace()),
            parcel::zero_or_more(join(
                expect_character('+').or(|| expect_character('-')),
                right(join(
                    zero_or_more(non_newline_whitespace()),
                    multiplication(),
                )),
            )),
        ))
        .map(unzip),
    )
    .map(|(lhe, (operators, mut operands))| {
        operands.insert(0, lhe);
        (operands, operators)
    })
    .map(|(operands, operators)| {
        let mut operands_iter = operands.into_iter().rev();
        let operators_iter = operators.into_iter().rev();
        let mut last: ExprNode = operands_iter.next().unwrap();

        for op in operators_iter {
            // this is fairly safe due to the parser guaranteeing enough args.
            let left = operands_iter.next().unwrap();
            last = match op {
                '+' => ExprNode::Addition(Box::new(left), Box::new(last)),
                '-' => ExprNode::Subtraction(Box::new(left), Box::new(last)),
                _ => panic!(format!("unexpected token: {}", op)),
            }
        }
        last
    })
    .or(|| multiplication())
}

#[allow(clippy::redundant_closure)]
fn multiplication<'a>() -> impl parcel::Parser<'a, &'a [char], ExprNode> {
    join(
        primary(),
        right(join(
            parcel::zero_or_more(non_newline_whitespace()),
            parcel::zero_or_more(join(
                expect_character('*').or(|| expect_character('/')),
                right(join(zero_or_more(non_newline_whitespace()), primary())),
            )),
        ))
        .map(unzip),
    )
    .map(|(lhe, (operators, mut operands))| {
        operands.insert(0, lhe);
        (operands, operators)
    })
    .map(|(operands, operators)| {
        let mut operands_iter = operands.into_iter().rev();
        let operators_iter = operators.into_iter().rev();
        let mut last: ExprNode = operands_iter.next().unwrap();

        for op in operators_iter {
            // this is fairly safe due to the parser guaranteeing enough args.
            let left = operands_iter.next().unwrap();
            last = match op {
                '*' => ExprNode::Multiplication(Box::new(left), Box::new(last)),
                '/' => ExprNode::Division(Box::new(left), Box::new(last)),
                _ => panic!(format!("unexpected token: {}", op)),
            }
        }
        last
    })
    .or(|| primary())
}

#[allow(clippy::redundant_closure)]
fn primary<'a>() -> impl parcel::Parser<'a, &'a [char], ExprNode> {
    number().map(|num| ExprNode::Number(num))
}

#[allow(clippy::redundant_closure)]
fn number<'a>() -> impl parcel::Parser<'a, &'a [char], Number> {
    dec_u64().map(|num| Number(num))
}

fn dec_u64<'a>() -> impl Parser<'a, &'a [char], u64> {
    move |input: &'a [char]| {
        let preparsed_input = input;
        let res = one_or_more(digit(10))
            .map(|digits| {
                let vd: String = digits.into_iter().collect();
                u64::from_str_radix(&vd, 10)
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

fn unzip<A, B>(pair: Vec<(A, B)>) -> (Vec<A>, Vec<B>) {
    let mut left_vec: Vec<A> = vec![];
    let mut right_vec: Vec<B> = vec![];
    pair.into_iter().for_each(|(left, right)| {
        left_vec.push(left);
        right_vec.push(right);
    });
    (left_vec, right_vec)
}
