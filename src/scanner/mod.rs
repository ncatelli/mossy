mod tokens;

pub struct ScanErr<T> {
    inner: T,
}

impl<T> ScanErr<T> {
    fn new(inner: T) -> Self {
        Self { inner }
    }
}

impl<T> std::fmt::Debug for ScanErr<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unable to scan: {:?}", self.inner)
    }
}

/// Positional represents a type with line and column metadata associated with it.
#[derive(Clone, Copy, PartialEq)]
pub struct Positional<T> {
    line: usize,
    col: usize,
    inner: T,
}

impl<T> Positional<T> {
    pub fn new(line: usize, col: usize, inner: T) -> Self {
        Self { line, col, inner }
    }
}

impl std::cmp::PartialEq<char> for Positional<char> {
    fn eq(&self, other: &char) -> bool {
        *other == self.inner
    }
}

impl<T> std::fmt::Debug for Positional<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "line: {}, column: {}, value: {:?}",
            self.line, self.col, self.inner
        )
    }
}

struct PositionalCharStreamIterator {
    inner: Vec<char>,
    index: usize,
    end: usize,
    line: usize,
    col: usize,
}

impl Iterator for PositionalCharStreamIterator {
    type Item = Positional<char>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.end {
            let c = self.inner[self.index].clone();

            // increment indexes
            self.index += 1;
            if c == '\n' {
                self.line += 1;
                self.col = 0;
            } else {
                self.col += 1;
            }

            Some(Positional::new(self.line, self.col, c))
        } else {
            None
        }
    }
}

impl PositionalCharStreamIterator {
    fn new(src: Vec<char>) -> Self {
        Self {
            index: 0,
            end: src.len(),
            line: 0,
            col: 0,

            inner: src,
        }
    }
}

pub fn scan<'a>(
    src: &'a [char],
) -> Result<Vec<Positional<tokens::Token>>, ScanErr<Positional<char>>> {
    PositionalCharStreamIterator::new(src.to_vec())
        .into_iter()
        .map(|pc| match pc.inner {
            '+' => Some(Ok(Positional::new(pc.line, pc.col, tokens::Token::PLUS))),
            '-' => Some(Ok(Positional::new(pc.line, pc.col, tokens::Token::MINUS))),
            '*' => Some(Ok(Positional::new(pc.line, pc.col, tokens::Token::STAR))),
            '/' => Some(Ok(Positional::new(pc.line, pc.col, tokens::Token::SLASH))),
            c if c.is_digit(10) => {
                let d = char::to_digit(c, 10).unwrap() as u8;
                Some(Ok(Positional::new(
                    pc.line,
                    pc.col,
                    tokens::Token::INTLITERAL(d),
                )))
            }
            c if c.is_whitespace() => None,
            _ => Some(Err(ScanErr::new(pc))),
        })
        .filter_map(|opt| opt)
        .collect()
}

#[cfg(test)]
mod tests {

    #[test]
    fn should_parse_sample_input() {
        let input = "2 + 3 * 5 - 8 / 3".chars().collect::<Vec<_>>();
        let output = super::scan(&input);
        assert!(super::scan(&input).is_ok());

        // should generate 9 tokens from the input
        assert_eq!(9, output.unwrap().len())
    }
}
