use parcel;
use parcel::prelude::v1::*;

mod tokens;

pub struct ScanErr;

pub fn scan<'a>(src: &'a [char]) -> Result<Vec<tokens::Token>, ScanErr> {
    parcel::left(parcel::join(
        parcel::one_or_more(token()),
        parcel::parsers::character::eof(),
    ))
    .parse(src)
    .map_err(|_| ScanErr)
    .and_then(|ms| match ms {
        MatchStatus::Match((_, toks)) => Ok(toks),
        MatchStatus::NoMatch(_) => Err(ScanErr),
    })
}

fn token<'a>() -> impl Parser<'a, &'a [char], tokens::Token> {
    parcel::one_of(vec![
        parcel::parsers::character::expect_character('+').map(|_| tokens::Token::PLUS),
        parcel::parsers::character::expect_character('+').map(|_| tokens::Token::MINUS),
        parcel::parsers::character::expect_character('+').map(|_| tokens::Token::STAR),
        parcel::parsers::character::expect_character('+').map(|_| tokens::Token::SLASH),
    ])
}
