//* Provides a foundation for the C pre-processor, encapsulated in the parser.

use parcel::prelude::v1::*;

type SpanEnumaratedChar = (usize, char);

/// Pre-processes the raw source input
pub fn pre_process(input: &[SpanEnumaratedChar]) -> Result<Vec<SpanEnumaratedChar>, String> {
    let enumerated_chars: Vec<(usize, SpanEnumaratedChar)> =
        input.iter().copied().enumerate().collect();

    let pre_processed_input = parcel::one_or_more(
        inline_comment()
            .map(|_| None)
            .or(|| block_comment().map(|_| None))
            .or(|| any_character().map(Some)),
    )
    .parse(&enumerated_chars[..])
    .and_then(|ms| match ms {
        MatchStatus::Match {
            span: _,
            remainder: _,
            inner,
        } => Ok(inner),
        MatchStatus::NoMatch(_) => Err("Unknown preprocessor error".to_string()),
    })
    .map(|post_process_chars| post_process_chars.into_iter().flatten().collect());

    pre_processed_input
}

fn expect_str<'a>(
    expected: &'static str,
) -> impl Parser<'a, &'a [(usize, SpanEnumaratedChar)], Vec<SpanEnumaratedChar>> {
    move |input: &'a [(usize, SpanEnumaratedChar)]| {
        let preparse_input = input;
        let expected_len = expected.len();
        let start_pos = preparse_input.first().map(|elem| elem.0).unwrap_or(0);
        let expected_end = start_pos + expected_len;
        let next: Vec<SpanEnumaratedChar> = input
            .iter()
            .take(expected_len)
            .copied()
            .map(|elem| elem.1)
            .collect();
        let next_str_repr: String = next.iter().map(|elem| elem.1).collect();

        if next_str_repr == expected {
            Ok(MatchStatus::Match {
                span: start_pos..expected_end,
                remainder: &input[expected_len..],
                inner: next,
            })
        } else {
            Ok(MatchStatus::NoMatch(preparse_input))
        }
    }
}

fn expect_character<'a>(
    expected: char,
) -> impl Parser<'a, &'a [(usize, SpanEnumaratedChar)], SpanEnumaratedChar> {
    move |input: &'a [(usize, SpanEnumaratedChar)]| match input.get(0) {
        Some(&(pos, next)) if next.1 == expected => Ok(MatchStatus::Match {
            span: pos..pos + 1,
            remainder: &input[1..],
            inner: next,
        }),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

fn any_character<'a>() -> impl Parser<'a, &'a [(usize, SpanEnumaratedChar)], SpanEnumaratedChar> {
    move |input: &'a [(usize, SpanEnumaratedChar)]| match input.get(0) {
        Some(&(pos, next)) => Ok(MatchStatus::Match {
            span: pos..pos + 1,
            remainder: &input[1..],
            inner: next,
        }),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

fn inline_comment<'a>() -> impl Parser<'a, &'a [(usize, SpanEnumaratedChar)], ()> {
    expect_str("//")
        .and_then(|_| parcel::zero_or_more(any_character().predicate(|&c| c.1 != '\n')))
        // eat the remain char
        .and_then(|_| expect_character('\n'))
        .map(|_| ())
}

fn block_comment<'a>() -> impl Parser<'a, &'a [(usize, SpanEnumaratedChar)], ()> {
    expect_str("/*").and_then(|_| {
        move |input: &'a [(usize, SpanEnumaratedChar)]| {
            let preparse_input = input;
            let start_span_pos = preparse_input.first().map(|elem| elem.0).unwrap_or(0);
            let mut start_offset = 0;

            while let Some([first, second]) = input.get(start_offset..start_offset + 2) {
                if [(first.1).1, (second.1).1] == ['*', '/'] {
                    let offset_from_start = second.0 - start_span_pos;

                    return Ok(MatchStatus::Match {
                        span: start_span_pos..second.0 + 1,
                        remainder: &input[offset_from_start + 1..],
                        inner: (),
                    });
                } else {
                    start_offset += 1
                }
            }
            Ok(MatchStatus::NoMatch(preparse_input))
        }
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn should_parse_inline_comments_from_arbitrary_source() {
        let input: Vec<(usize, char)> = "{ 5; // test\n}".chars().enumerate().collect();

        let res = super::pre_process(&input).map(|post_process_chars| {
            post_process_chars
                .into_iter()
                .map(|positional_char| positional_char.1)
                .collect::<String>()
        });

        assert_eq!(Ok("{ 5; }".to_string()), res);
    }

    #[test]
    fn should_parse_block_comments_from_arbitrary_source() {
        let input: Vec<(usize, char)> = "{ /* test */ 5; }".chars().enumerate().collect();
        let res = super::pre_process(&input).map(|post_process_chars| {
            post_process_chars
                .into_iter()
                .map(|positional_char| positional_char.1)
                .collect::<String>()
        });

        assert_eq!(Ok("{  5; }".to_string()), res);
    }
}
