use std::char;

use parcel;
use parcel::prelude::v1::*;

mod tokens;

pub struct ScanErr;

pub fn scan<'a>(src: &'a [char]) -> Result<Vec<tokens::Token>, ScanErr> {
    parcel::left(parcel::join(
        parcel::one_or_more(token()),
        parcel::zero_or_more(parcel::parsers::character::whitespace())
            .and_then(|_| parcel::parsers::character::eof()),
    ))
    .parse(src)
    .map_err(|_| ScanErr)
    .and_then(|ms| match ms {
        MatchStatus::Match((_, toks)) => Ok(toks
            .into_iter()
            .chain(vec![tokens::Token::EOF].into_iter())
            .collect()),
        MatchStatus::NoMatch(_) => Err(ScanErr),
    })
}

fn token<'a>() -> impl Parser<'a, &'a [char], tokens::Token> {
    parcel::optional(parcel::parsers::character::whitespace())
        .and_then(|_| integer_literal().or(|| special_characters()))
}

fn integer_literal<'a>() -> impl Parser<'a, &'a [char], tokens::Token> {
    parcel::parsers::character::digit(10).map(|digit| {
        // this should never be in a case that it shouldn't match a valid
        //digit.
        let d = char::to_digit(digit, 10).unwrap() as u8;
        tokens::Token::INTLITERAL(d)
    })
}

fn special_characters<'a>() -> impl Parser<'a, &'a [char], tokens::Token> {
    parcel::one_of(vec![
        parcel::parsers::character::expect_character('+').map(|_| tokens::Token::PLUS),
        parcel::parsers::character::expect_character('-').map(|_| tokens::Token::MINUS),
        parcel::parsers::character::expect_character('*').map(|_| tokens::Token::STAR),
        parcel::parsers::character::expect_character('/').map(|_| tokens::Token::SLASH),
    ])
}
