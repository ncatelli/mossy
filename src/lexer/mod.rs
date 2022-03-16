mod stack;

/// Defines the wrapper type for an error returned from Lexing
type LexError = String;

/// Lex returns either a
pub type LexResult = Result<Vec<Token>, LexError>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenType {
    Eof,

    // Binary operators
    Equal,
    EqualEqual,
    Pipe,
    PipePipe,
    Ampersand,
    AmpersandAmpersand,
    Carat,
    Bang,
    BangEqual,
    LessThan,
    GreaterThan,
    LessEqual,
    GreaterEqual,
    LShift,
    RShift,
    Plus,
    Minus,
    Star,
    Slash,
    PercentSign,

    // Other operators
    Tilde,
    PlusPlus,
    MinusMinus,

    // Type keywords
    Signed,
    Unsigned,
    Void,
    Char,
    Short,
    Int,
    Long,

    // Other keywords
    If,
    Else,
    While,
    For,
    Return,

    // Structural tokens
    CharLiteral,
    IntLiteral,
    StrLiteral,
    SemiColon,
    Identifier,
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    Eof,

    // Binary operators
    Equal,
    EqualEqual,
    Pipe,
    PipePipe,
    Ampersand,
    AmpersandAmperand,
    Carat,
    Bang,
    BangEqual,
    LessThan,
    GreaterThan,
    LessEqual,
    GreaterEqual,
    LShift,
    RShift,
    Plus,
    Minus,
    Star,
    Slash,
    PercentSign,

    // Other operators
    Tilde,
    PlusPlus,
    MinusMinus,

    // Type keywords
    Signed,
    Unsigned,
    Void,
    Char,
    Short,
    Int,
    Long,

    // Other keywords
    If,
    Else,
    While,
    For,
    Return,

    // Structural tokens
    CharLiteral(char),
    IntLiteral(isize),
    StrLiteral(String),
    Identifier(String),
    SemiColon,
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
}

impl Token {
    pub fn to_token_type(&self) -> TokenType {
        match self {
            Token::Eof => TokenType::Eof,
            Token::Equal => TokenType::Equal,
            Token::Pipe => TokenType::Pipe,
            Token::AmpersandAmperand => TokenType::AmpersandAmpersand,
            Token::PipePipe => TokenType::PipePipe,
            Token::Carat => TokenType::Carat,
            Token::Ampersand => TokenType::Ampersand,
            Token::EqualEqual => TokenType::EqualEqual,
            Token::Bang => TokenType::Bang,
            Token::BangEqual => TokenType::BangEqual,
            Token::LessThan => TokenType::LessThan,
            Token::GreaterThan => TokenType::GreaterThan,
            Token::LessEqual => TokenType::LessEqual,
            Token::GreaterEqual => TokenType::GreaterEqual,
            Token::LShift => TokenType::LShift,
            Token::RShift => TokenType::RShift,
            Token::Plus => TokenType::Plus,
            Token::Minus => TokenType::Minus,
            Token::Star => TokenType::Star,
            Token::Slash => TokenType::Slash,
            Token::PercentSign => TokenType::PercentSign,
            Token::Tilde => TokenType::Tilde,
            Token::PlusPlus => TokenType::PlusPlus,
            Token::MinusMinus => TokenType::MinusMinus,
            Token::Signed => TokenType::Signed,
            Token::Unsigned => TokenType::Unsigned,
            Token::Void => TokenType::Void,
            Token::Char => TokenType::Char,
            Token::Short => TokenType::Short,
            Token::Int => TokenType::Int,
            Token::Long => TokenType::Long,
            Token::If => TokenType::If,
            Token::Else => TokenType::Else,
            Token::While => TokenType::While,
            Token::For => TokenType::For,
            Token::Return => TokenType::Return,
            Token::CharLiteral(_) => TokenType::CharLiteral,
            Token::IntLiteral(_) => TokenType::IntLiteral,
            Token::StrLiteral(_) => TokenType::StrLiteral,
            Token::Identifier(_) => TokenType::Identifier,
            Token::SemiColon => TokenType::SemiColon,
            Token::LBrace => TokenType::LBrace,
            Token::RBrace => TokenType::RBrace,
            Token::LParen => TokenType::LParen,
            Token::RParen => TokenType::RParen,
            Token::LBracket => TokenType::LBracket,
            Token::RBracket => TokenType::RBracket,
            Token::Comma => TokenType::Comma,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Cursor {
    index: usize,
    col: usize,
    line: usize,
}

impl Cursor {
    pub fn increment_column_mut(&mut self) {
        self.index += 1;
        self.col += 1;
    }

    pub fn increment_line_mut(&mut self) {
        self.index += 1;
        self.line += 1;
        self.col += 0;
    }
}

impl Default for Cursor {
    fn default() -> Self {
        Self {
            index: 0,
            col: 0,
            line: 1,
        }
    }
}

impl core::fmt::Display for Cursor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line: {}, column: {}", self.line, self.col)
    }
}

use std::iter::Iterator;

const STACK_SIZE: usize = 4096;

type LexerStack<const N: usize> = stack::Stack<TokenOrLexeme, N>;

const TOKEN_OR_LEXEME_INITIALIZER: TokenOrLexeme = TokenOrLexeme::Lexeme('\x00');

#[derive(Debug, Clone)]
enum TokenOrLexeme {
    Token(Token),
    Lexeme(char),
}

impl TokenOrLexeme {
    fn to_lexeme(&self) -> Option<char> {
        match self {
            TokenOrLexeme::Lexeme(c) => Some(*c),
            TokenOrLexeme::Token(_) => None,
        }
    }
}

impl Default for TokenOrLexeme {
    fn default() -> Self {
        TOKEN_OR_LEXEME_INITIALIZER
    }
}

macro_rules! token {
    ($tok:expr) => {
        TokenOrLexeme::Token($tok)
    };
}

macro_rules! lexeme {
    ($lexeme:literal) => {
        TokenOrLexeme::Lexeme($lexeme)
    };
    ($lexeme:expr) => {
        TokenOrLexeme::Lexeme($lexeme)
    };
}

#[derive(Debug, Clone, Copy)]
enum EscapedAscii {
    /// Character was escaped
    Escaped(char),
    /// Represents a standard character
    NonEscaped(char),
}

impl EscapedAscii {
    fn unwrap(self) -> char {
        match self {
            Self::Escaped(c) | Self::NonEscaped(c) => c,
        }
    }
}

fn to_ascii_escaped_char(c: char) -> EscapedAscii {
    use EscapedAscii::*;

    match c {
        '0' => Escaped('\0'),
        't' => Escaped('\t'),
        'n' => Escaped('\n'),
        other => NonEscaped(other),
    }
}

#[derive(Debug)]
enum LexOperation<T> {
    // the last n elements to pop off and the target type
    Shift(T),
    ShiftReduce(usize, T),
    Reduce(usize, T),
    NoFurtherRefinement,
    Err(String),
}

fn lexeme_is_identifier_ascii() -> impl Fn(&TokenOrLexeme) -> bool {
    move |tol: &TokenOrLexeme| matches!(tol, TokenOrLexeme::Lexeme(l) if l.is_ascii_alphanumeric() || *l == '_')
}

fn matches_rules<T>(src: &[T], pred: impl Fn(&T) -> bool) -> bool {
    src.iter().all(pred)
}

fn stack_eval_to_token(stack: &[TokenOrLexeme], next: Option<char>) -> LexOperation<TokenOrLexeme> {
    match (stack, next) {
        // shift an empty stack
        ([], Some(c)) => LexOperation::Shift(lexeme!(c)),

        ([lexeme!('{')], _) => LexOperation::Reduce(1, token!(Token::LBrace)),
        ([lexeme!('}')], _) => LexOperation::Reduce(1, token!(Token::RBrace)),
        ([lexeme!('(')], _) => LexOperation::Reduce(1, token!(Token::LParen)),
        ([lexeme!(')')], _) => LexOperation::Reduce(1, token!(Token::RParen)),
        ([lexeme!('[')], _) => LexOperation::Reduce(1, token!(Token::LBracket)),
        ([lexeme!(']')], _) => LexOperation::Reduce(1, token!(Token::RBracket)),
        ([lexeme!(';')], _) => LexOperation::Reduce(1, token!(Token::SemiColon)),
        ([lexeme!(',')], _) => LexOperation::Reduce(1, token!(Token::Comma)),

        ([TokenOrLexeme::Token(Token::Equal)], Some('=')) => {
            LexOperation::ShiftReduce(2, token!(Token::EqualEqual))
        }
        ([lexeme!('=')], _) => LexOperation::Reduce(1, token!(Token::Equal)),
        ([TokenOrLexeme::Token(Token::Bang)], Some('=')) => {
            LexOperation::ShiftReduce(2, token!(Token::BangEqual))
        }
        ([lexeme!('!')], _) => LexOperation::Reduce(1, token!(Token::Bang)),

        ([TokenOrLexeme::Token(Token::GreaterThan)], Some('>')) => {
            LexOperation::ShiftReduce(2, token!(Token::RShift))
        }
        ([TokenOrLexeme::Token(Token::GreaterThan)], Some('=')) => {
            LexOperation::ShiftReduce(2, token!(Token::GreaterEqual))
        }
        ([lexeme!('>')], _) => LexOperation::Reduce(1, token!(Token::GreaterThan)),

        ([TokenOrLexeme::Token(Token::LessThan)], Some('<')) => {
            LexOperation::ShiftReduce(2, token!(Token::LShift))
        }
        ([TokenOrLexeme::Token(Token::LessThan)], Some('=')) => {
            LexOperation::ShiftReduce(2, token!(Token::LessEqual))
        }
        ([lexeme!('<')], _) => LexOperation::Reduce(1, token!(Token::LessThan)),

        ([TokenOrLexeme::Token(Token::Ampersand)], Some('&')) => {
            LexOperation::ShiftReduce(2, token!(Token::AmpersandAmperand))
        }
        ([lexeme!('&')], _) => LexOperation::Reduce(1, token!(Token::Ampersand)),

        ([TokenOrLexeme::Token(Token::Pipe)], Some('|')) => {
            LexOperation::ShiftReduce(2, token!(Token::PipePipe))
        }
        ([lexeme!('|')], _) => LexOperation::Reduce(1, token!(Token::Pipe)),

        ([lexeme!('^')], _) => LexOperation::Reduce(1, token!(Token::Carat)),
        ([lexeme!('~')], _) => LexOperation::Reduce(1, token!(Token::Tilde)),

        ([TokenOrLexeme::Token(Token::Plus)], Some('+')) => {
            LexOperation::ShiftReduce(2, token!(Token::PlusPlus))
        }
        ([lexeme!('+')], _) => LexOperation::Reduce(1, token!(Token::Plus)),
        ([TokenOrLexeme::Token(Token::Minus)], Some('-')) => {
            LexOperation::ShiftReduce(2, token!(Token::MinusMinus))
        }
        ([lexeme!('-')], _) => LexOperation::Reduce(1, token!(Token::Minus)),

        ([lexeme!('*')], _) => LexOperation::Reduce(1, token!(Token::Star)),
        ([lexeme!('/')], _) => LexOperation::Reduce(1, token!(Token::Slash)),

        ([lexeme!('\''), TokenOrLexeme::Lexeme(c), lexeme!('\'')], _) if c.is_ascii() => {
            LexOperation::Reduce(3, token!(Token::CharLiteral(*c)))
        }
        ([lexeme!('\'')], Some(l)) if l.is_ascii() || l == '\\' => LexOperation::Shift(lexeme!(l)),
        ([lexeme!('\''), TokenOrLexeme::Lexeme('\\'), TokenOrLexeme::Lexeme(c)], Some('\''))
            if c.is_ascii() =>
        {
            let escaped = to_ascii_escaped_char(*c).unwrap();
            LexOperation::ShiftReduce(4, token!(Token::CharLiteral(escaped)))
        }
        ([lexeme!('\''), TokenOrLexeme::Lexeme(c)], Some('\'')) if c.is_ascii() => {
            LexOperation::ShiftReduce(3, token!(Token::CharLiteral(*c)))
        }

        ([lexeme!('\"'), .., lexeme!('\\')], Some('\"')) => LexOperation::Shift(lexeme!('\"')),
        ([lexeme!('\"'), inner @ ..], Some('\"')) => {
            let inner_str = inner
                .iter()
                .flat_map(|tol| match tol {
                    TokenOrLexeme::Token(_) => None,
                    TokenOrLexeme::Lexeme(c) => Some(*c),
                })
                .collect();
            let token_cnt = inner.len() + 2;
            LexOperation::ShiftReduce(token_cnt, token!(Token::StrLiteral(inner_str)))
        }
        ([lexeme!('\"'), ..], Some(c)) => LexOperation::Shift(lexeme!(c)),

        ([TokenOrLexeme::Lexeme(l)], _) if l.is_digit(10) => l
            .to_digit(10)
            .map(|d| d as isize)
            .map(|lit| LexOperation::Reduce(1, token!(Token::IntLiteral(lit))))
            .unwrap_or_else(|| LexOperation::Err(format!("Unable to convert {} to digit", l))),
        ([TokenOrLexeme::Token(Token::IntLiteral(_))], Some(l)) if l.is_digit(10) => {
            LexOperation::Shift(lexeme!(l))
        }
        ([TokenOrLexeme::Token(Token::IntLiteral(base_int_lit)), TokenOrLexeme::Lexeme(l)], _)
            if l.is_digit(10) =>
        {
            l.to_digit(10)
                .map(|d| d as isize)
                .map(|next| {
                    // This match guarantees there is atleast a base.
                    // if that base is < 10 we need to scale it.
                    let unadjusted_multiplier = (base_int_lit / 10) as u32;
                    let multiplier = if unadjusted_multiplier == 0 {
                        1
                    } else {
                        unadjusted_multiplier
                    };

                    let scaled_base = base_int_lit * 10isize.pow(multiplier);
                    let new_lit = scaled_base + next;

                    LexOperation::Reduce(2, token!(Token::IntLiteral(new_lit)))
                })
                .unwrap_or_else(|| LexOperation::Err(format!("Unable to convert {} to digit", l)))
        }

        // Identifiers
        ([contents @ ..], Some(l))
            if matches_rules(contents, lexeme_is_identifier_ascii())
                && matches_rules(&[lexeme!(l)], lexeme_is_identifier_ascii()) =>
        {
            LexOperation::Shift(lexeme!(l))
        }
        // if lookahead doesn't match an identifier reduce
        ([contents @ ..], Some(l))
            if matches_rules(contents, lexeme_is_identifier_ascii())
                && !matches_rules(&[lexeme!(l)], lexeme_is_identifier_ascii()) =>
        {
            LexOperation::Reduce(
                contents.len(),
                token!(Token::Identifier(
                    contents
                        .iter()
                        .flat_map(|tol| tol.to_lexeme())
                        .collect::<String>()
                )),
            )
        }
        // if lookahead is empty, reduce.
        ([contents @ ..], None) if matches_rules(contents, lexeme_is_identifier_ascii()) => {
            LexOperation::Reduce(
                contents.len(),
                token!(Token::Identifier(
                    contents
                        .iter()
                        .flat_map(|tol| tol.to_lexeme())
                        .collect::<String>()
                )),
            )
        }

        // Type Keywords
        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "signed" => {
            LexOperation::Reduce(1, token!(Token::Signed))
        }
        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "unsigned" => {
            LexOperation::Reduce(1, token!(Token::Unsigned))
        }
        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "void" => {
            LexOperation::Reduce(1, token!(Token::Void))
        }
        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "char" => {
            LexOperation::Reduce(1, token!(Token::Char))
        }
        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "short" => {
            LexOperation::Reduce(1, token!(Token::Short))
        }
        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "int" => {
            LexOperation::Reduce(1, token!(Token::Int))
        }
        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "long" => {
            LexOperation::Reduce(1, token!(Token::Long))
        }

        // Other keywords
        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "if" => {
            LexOperation::Reduce(1, token!(Token::If))
        }
        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "else" => {
            LexOperation::Reduce(1, token!(Token::Else))
        }
        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "for" => {
            LexOperation::Reduce(1, token!(Token::For))
        }
        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "while" => {
            LexOperation::Reduce(1, token!(Token::While))
        }

        ([TokenOrLexeme::Token(Token::Identifier(id))], _) if id == "return" => {
            LexOperation::Reduce(1, token!(Token::Return))
        }

        ([TokenOrLexeme::Token(_)], _) | ([.., TokenOrLexeme::Token(_)], _) => {
            LexOperation::NoFurtherRefinement
        }
        ([.., TokenOrLexeme::Lexeme(c)], _) if c.is_whitespace() => {
            LexOperation::Reduce(1, lexeme!(*c))
        }

        _ => LexOperation::Err("No rules matched with unpaired lexemes.".to_string()),
    }
}

/// Scanner takes a string representing lox source and attempts to convert the
/// source into a vector of either Tokens or lexical errors.
pub struct Scanner<'a> {
    source: core::iter::Peekable<core::str::Chars<'a>>,
    cursor: Cursor,
    stack: LexerStack<STACK_SIZE>,
    end: usize,
}

fn consume_and_peek_from_iter<I>(iter: &mut core::iter::Peekable<I>) -> Option<char>
where
    I: Iterator<Item = char>,
{
    let _ = iter.next();
    iter.peek().copied()
}

impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Scanner<'a> {
        let stack = LexerStack::new([TOKEN_OR_LEXEME_INITIALIZER; STACK_SIZE]);
        let end = source.len();
        Scanner {
            source: source.chars().peekable(),
            cursor: Cursor::default(),
            stack,
            end,
        }
    }

    fn is_empty(&self) -> bool {
        let index = self.cursor.index;
        index >= self.end
    }

    fn scan_token_from(&mut self) -> Result<Token, String> {
        if self.source.peek().is_none() {
            Ok(Token::Eof)
        } else {
            let mut lookahead = self.source.peek().copied();
            loop {
                let stack = self.stack.as_ref();
                let op = stack_eval_to_token(stack, lookahead);

                match op {
                    LexOperation::Shift(TokenOrLexeme::Lexeme('\n')) => {
                        // safe to unwrap due to is_some guarantee
                        self.stack.push_mut(lexeme!('\n'));
                        lookahead = consume_and_peek_from_iter(&mut self.source);
                        self.cursor.increment_line_mut();
                    }
                    LexOperation::Shift(next_val) => {
                        // safe to unwrap due to is_some guarantee
                        self.stack.push_mut(next_val);
                        lookahead = consume_and_peek_from_iter(&mut self.source);
                        self.cursor.increment_column_mut();
                    }
                    LexOperation::ShiftReduce(by, TokenOrLexeme::Token(to_token)) => {
                        lookahead = consume_and_peek_from_iter(&mut self.source);
                        // pop n elements off the stack
                        for _ in 0..by {
                            self.stack.pop_mut();
                        }

                        self.stack.push_mut(TokenOrLexeme::Token(to_token));
                        // safe to unwrap due to is_some guarantee
                        self.cursor.increment_column_mut();
                    }
                    LexOperation::ShiftReduce(by, TokenOrLexeme::Lexeme('\n')) => {
                        for _ in 0..by {
                            self.stack.pop_mut();
                        }
                        self.cursor.increment_line_mut();
                    }
                    LexOperation::ShiftReduce(by, TokenOrLexeme::Lexeme(_)) => {
                        for _ in 0..by {
                            self.stack.pop_mut();
                        }
                        self.cursor.increment_column_mut();
                    }
                    LexOperation::Reduce(by, TokenOrLexeme::Lexeme('\n')) => {
                        for _ in 0..by {
                            self.stack.pop_mut();
                        }
                    }
                    // this will only occur with whitespace
                    LexOperation::Reduce(by, TokenOrLexeme::Lexeme(_)) => {
                        for _ in 0..by {
                            self.stack.pop_mut();
                        }
                    }

                    LexOperation::Reduce(by, tol) => {
                        // pop n elements off the stack
                        for _ in 0..by {
                            self.stack.pop_mut();
                        }

                        // push the new token and next lexeme onto the stack.
                        self.stack.push_mut(tol);
                    }
                    LexOperation::NoFurtherRefinement => match self.stack.pop_mut() {
                        Some(TokenOrLexeme::Token(tok)) => return Ok(tok),
                        _ => return Err(format!("invalid token at {}", &self.cursor)),
                    },

                    LexOperation::Err(e) => return Err(format!("{} at {}", e, &self.cursor)),
                }
            }
        }
    }
}

impl<'a> IntoIterator for Scanner<'a> {
    type Item = Result<Token, String>;
    type IntoIter = ScannerIntoIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        ScannerIntoIterator { scanner: self }
    }
}

pub struct ScannerIntoIterator<'a> {
    scanner: Scanner<'a>,
}

impl<'a> Iterator for ScannerIntoIterator<'a> {
    type Item = Result<Token, String>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.scanner.is_empty() {
            None
        } else {
            let next = self.scanner.scan_token_from();
            match next {
                Ok(Token::Eof) => None,
                lex_res @ Ok(_) => Some(lex_res),
                lex_res @ Err(_) => Some(lex_res),
            }
        }
    }
}

/// lex all tokens into a a result vector. This should almost always be used directly as an iterator over
/// the scanner.
///
/// # Notes
/// This requires a needless collect to prevent a stack error.
#[allow(clippy::needless_collect)]
pub fn lex(src: &str) -> LexResult {
    let scanner = Scanner::new(src);
    let tokens: Vec<Result<Token, LexError>> = scanner.into_iter().collect();
    let collected_result: Result<Vec<Token>, String> = tokens.into_iter().collect();
    collected_result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_scan_single_token() {
        let inputs = ["{", " {", " { "];

        for input in inputs {
            let mut scanner = Scanner::new(input).into_iter();

            assert_eq!(Some(Ok(Token::LBrace)), scanner.next())
        }
    }

    #[test]
    fn should_scan_compound_token() {
        let input_expected = [
            (["<", " <", " < "], Token::LessThan),
            (["<=", " <=", " <= "], Token::LessEqual),
        ];

        for (inputs, expected) in input_expected {
            for input in inputs {
                let mut scanner = Scanner::new(input).into_iter();

                assert_eq!(Some(Ok(expected.clone())), scanner.next())
            }
        }
    }

    #[test]
    fn should_scan_digit_token() {
        let input_expected = [
            (["1", " 1", " 1 "], Token::IntLiteral(1)),
            (["123", " 123", " 123 "], Token::IntLiteral(123)),
        ];

        for (inputs, expected) in input_expected {
            for input in inputs {
                let mut scanner = Scanner::new(input).into_iter();

                assert_eq!(Some(Ok(expected.clone())), scanner.next())
            }
        }
    }

    #[test]
    fn should_scan_char_literals() {
        let input_expected = [
            (["\'a\'"], Token::CharLiteral('a')),
            ([" \'a\'"], Token::CharLiteral('a')),
            ([" \'a\' "], Token::CharLiteral('a')),
            (["\'\t\'"], Token::CharLiteral('\t')),
            ([" \'\t\'"], Token::CharLiteral('\t')),
            ([" \'\t\' "], Token::CharLiteral('\t')),
        ];

        for (inputs, expected) in input_expected {
            for input in inputs {
                let mut scanner = Scanner::new(input).into_iter();

                assert_eq!(Some(Ok(expected.clone())), scanner.next())
            }
        }
    }

    #[test]
    fn should_scan_string_literals() {
        let input_expected = [
            (["\"hello\""], Token::StrLiteral("hello".to_string())),
            ([" \"hello\""], Token::StrLiteral("hello".to_string())),
            ([" \"hello\" "], Token::StrLiteral("hello".to_string())),
        ];

        for (inputs, expected) in input_expected {
            for input in inputs {
                let mut scanner = Scanner::new(input).into_iter();

                assert_eq!(Some(Ok(expected.clone())), scanner.next())
            }
        }
    }

    #[test]
    fn should_scan_identifier() {
        let input_expected = [
            (["test"], Token::Identifier("test".to_string())),
            ([" test"], Token::Identifier("test".to_string())),
            ([" test "], Token::Identifier("test".to_string())),
        ];

        for (inputs, expected) in input_expected {
            for input in inputs {
                let mut scanner = Scanner::new(input).into_iter();

                assert_eq!(Some(Ok(expected.clone())), scanner.next())
            }
        }
    }

    #[test]
    fn should_scan_keywords() {
        let input_expected = [
            (["for"], Token::For),
            ([" for"], Token::For),
            ([" for "], Token::For),
        ];

        for (inputs, expected) in input_expected {
            for input in inputs {
                let mut scanner = Scanner::new(input).into_iter();

                assert_eq!(Some(Ok(expected.clone())), scanner.next())
            }
        }
    }

    #[test]
    fn should_scan_multiple_tokens() {
        let input = "{ 1 + 2; }";
        let res = lex(input);

        let expected: Result<Vec<_>, _> = Ok(vec![
            Token::LBrace,
            Token::IntLiteral(1),
            Token::Plus,
            Token::IntLiteral(2),
            Token::SemiColon,
            Token::RBrace,
        ]);

        assert_eq!(expected, res)
    }
}
