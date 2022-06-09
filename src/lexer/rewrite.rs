/// Defines the wrapper type for an error returned from Lexing
type LexError = String;

/// Lex returns either a
pub type LexResult<'a> = Result<Vec<Token<'a>>, LexError>;

/// Provides metadata about the classification of a given Token.
#[derive(Debug)]
#[allow(unused)]
pub enum TokenClass {
    Identifier,
    Keywords,
    Constant,
    StringLiteral,
    Operator,
    Separator,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    Identifier,

    // Constants
    FloatConstant,
    CharacterConstant,
    IntegerConstant,

    StringLiteral,

    // Keywords
    Auto,
    Break,
    Case,
    Char,
    Const,
    Continue,
    Default,
    Do,
    Double,
    Else,
    Enum,
    Extern,
    Float,
    For,
    Goto,
    If,
    Int,
    Long,
    Register,
    Return,
    Short,
    Signed,
    SizeOf,
    Static,
    Struct,
    Switch,
    TypeDef,
    Union,
    Unsigned,
    Void,
    Volatile,
    While,

    // Operators
    Ampersand,
    AmpersandAmpersand,
    AmpersandEqual,
    Arrow,
    Bang,
    BangEqual,
    Caret,
    CaretEqual,
    Colon,
    Comma,
    Dot,
    Equal,
    EqualEqual,
    GreaterEqual,
    GreaterThan,
    LeftBrace,
    LeftBracket,
    LeftParen,
    LeftShift,
    LeftShiftEqual,
    LessEqual,
    LessThan,
    Minus,
    MinusEqual,
    MinusMinus,
    PercentEqual,
    PercentSign,
    Pipe,
    PipeEqual,
    PipePipe,
    Plus,
    PlusEqual,
    PlusPlus,
    Question,
    RightBrace,
    RightBracket,
    RightParen,
    RightShift,
    RightShiftEqual,
    Slash,
    SlashEqual,
    Star,
    StarEqual,
    Tilde,

    // Separators
    SemiColon,
}

impl TokenKind {
    pub fn token_class(&self) -> TokenClass {
        match self {
            TokenKind::Auto
            | TokenKind::Break
            | TokenKind::Case
            | TokenKind::Char
            | TokenKind::Const
            | TokenKind::Continue
            | TokenKind::Default
            | TokenKind::Do
            | TokenKind::Double
            | TokenKind::Else
            | TokenKind::Enum
            | TokenKind::Extern
            | TokenKind::Float
            | TokenKind::For
            | TokenKind::Goto
            | TokenKind::If
            | TokenKind::Int
            | TokenKind::Long
            | TokenKind::Register
            | TokenKind::Return
            | TokenKind::Short
            | TokenKind::Signed
            | TokenKind::SizeOf
            | TokenKind::Static
            | TokenKind::Struct
            | TokenKind::Switch
            | TokenKind::TypeDef
            | TokenKind::Union
            | TokenKind::Unsigned
            | TokenKind::Void
            | TokenKind::Volatile
            | TokenKind::While => TokenClass::Keywords,

            TokenKind::FloatConstant
            | TokenKind::IntegerConstant
            | TokenKind::CharacterConstant => TokenClass::Constant,

            TokenKind::StringLiteral => TokenClass::StringLiteral,

            TokenKind::Identifier => TokenClass::Identifier,

            TokenKind::Ampersand
            | TokenKind::AmpersandAmpersand
            | TokenKind::AmpersandEqual
            | TokenKind::Arrow
            | TokenKind::Bang
            | TokenKind::BangEqual
            | TokenKind::Caret
            | TokenKind::CaretEqual
            | TokenKind::Colon
            | TokenKind::Comma
            | TokenKind::Dot
            | TokenKind::Equal
            | TokenKind::EqualEqual
            | TokenKind::GreaterEqual
            | TokenKind::GreaterThan
            | TokenKind::LeftBrace
            | TokenKind::LeftBracket
            | TokenKind::LeftParen
            | TokenKind::LeftShift
            | TokenKind::LeftShiftEqual
            | TokenKind::LessEqual
            | TokenKind::LessThan
            | TokenKind::Minus
            | TokenKind::MinusEqual
            | TokenKind::MinusMinus
            | TokenKind::PercentEqual
            | TokenKind::PercentSign
            | TokenKind::Pipe
            | TokenKind::PipeEqual
            | TokenKind::PipePipe
            | TokenKind::Plus
            | TokenKind::PlusEqual
            | TokenKind::PlusPlus
            | TokenKind::Question
            | TokenKind::RightBrace
            | TokenKind::RightBracket
            | TokenKind::RightParen
            | TokenKind::RightShift
            | TokenKind::RightShiftEqual
            | TokenKind::Slash
            | TokenKind::SlashEqual
            | TokenKind::Star
            | TokenKind::StarEqual
            | TokenKind::Tilde => TokenClass::Operator,

            // Separator
            TokenKind::SemiColon => TokenClass::Separator,
        }
    }
}

/// Provides input tracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cursor {
    index: usize,
    col: usize,
    line: usize,
}

impl Cursor {
    pub const fn new(index: usize, col: usize, line: usize) -> Self {
        Self { index, col, line }
    }

    pub fn increment_column(mut self) -> Self {
        self.increment_column_mut();
        self
    }

    pub fn increment_column_mut(&mut self) {
        self.index += 1;
        self.col += 1;
    }

    pub fn increment_line(mut self) -> Self {
        self.increment_line_mut();
        self
    }

    pub fn increment_line_mut(&mut self) {
        self.index += 1;
        self.line += 1;
        self.col = 0;
    }
}

impl Default for Cursor {
    fn default() -> Self {
        Self::new(0, 0, 1)
    }
}

impl core::fmt::Display for Cursor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line: {}, column: {}", self.line, self.col)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    start: Cursor,
    end: Cursor,
}

impl Span {
    pub fn new(start: Cursor, end: Cursor) -> Self {
        Self { start, end }
    }
}

impl From<Span> for std::ops::Range<usize> {
    fn from(span: Span) -> Self {
        let start = span.start.index;
        let end = span.end.index;

        start..end
    }
}

impl core::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})..({})", self.start, self.end)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token<'a> {
    pub span: Span,
    pub data: Option<&'a str>,
    pub kind: TokenKind,
}

impl<'a> Token<'a> {
    pub fn new(span: Span, kind: TokenKind) -> Self {
        Self {
            span,
            data: None,
            kind,
        }
    }

    pub fn with_data(span: Span, data: &'a str, kind: TokenKind) -> Self {
        Self {
            span,
            data: Some(data),
            kind,
        }
    }

    /// Returns the token's kind.
    pub fn as_kind(&self) -> TokenKind {
        self.kind
    }

    /// Returns the slice of a given input that a token represents. If the
    /// token is out of range for an input, None is returned.
    pub fn str_from_input(&self, input: &'a str) -> Option<&'a str> {
        let range: std::ops::Range<_> = self.span.into();

        input.get(range)
    }
}

use std::iter::Iterator;

const STACK_SIZE: usize = 2048;

type LexerStack<'a, const N: usize> = super::stack::Stack<TokenOrLexeme<'a>, N>;

const TOKEN_OR_LEXEME_INITIALIZER: TokenOrLexeme =
    TokenOrLexeme::Lexeme(Cursor::new(0, 0, 1), '\x00');

#[derive(Debug, Clone)]
enum TokenOrLexeme<'a> {
    Token(Token<'a>),
    Lexeme(Cursor, char),
}

impl<'a> Default for TokenOrLexeme<'a> {
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
    ($cursor:expr, $lexeme:literal) => {
        TokenOrLexeme::Lexeme($cursor, $lexeme)
    };
    ($cursor:expr, $lexeme:expr) => {
        TokenOrLexeme::Lexeme($cursor, $lexeme)
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
enum AdvanceOperation {
    IncrementLine,
    IncrementColumn,
}

#[derive(Debug)]
enum LexOperation<T> {
    // the last n elements to pop off and the target type
    Shift(T),
    ShiftReduce(usize, T),
    Reduce(usize, T),
    NoFurtherRefinement,
    // usize represents an optional number of tokens to purge off the stack
    // when advancing.
    Advance(usize, AdvanceOperation),
    Err(String),
}

fn lexeme_is_identifier_ascii() -> impl Fn(&TokenOrLexeme) -> bool {
    move |tol: &TokenOrLexeme| matches!(tol, TokenOrLexeme::Lexeme(_, l) if l.is_ascii_alphanumeric() || *l == '_')
}

fn matches_rules<T>(src: &[T], pred: impl Fn(&T) -> bool) -> bool {
    src.iter().all(pred)
}

fn stack_eval_to_token<'a>(
    source: &'a str,
    stack: &[TokenOrLexeme],
    next: Option<(Cursor, char)>,
) -> LexOperation<TokenOrLexeme<'a>> {
    match (stack, next) {
        // shift an empty stack
        ([], Some((cursor, ch))) => LexOperation::Shift(lexeme!(cursor, ch)),

        ([TokenOrLexeme::Lexeme(cur, '{')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::LeftBrace
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '}')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::RightBrace
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '(')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::LeftParen
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, ')')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::RightParen
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '[')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::LeftBracket
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, ']')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::RightBracket
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, ';')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::SemiColon
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, ':')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Colon
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, ',')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Comma
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '.')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Dot
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '?')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Question
            )),
        ),

        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Minus,
                ..
            })],
            Some((end, '>')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::Arrow,
            )),
        ),
        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Equal,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::EqualEqual,
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '=')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Equal
            )),
        ),
        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Bang,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::BangEqual
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '!')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Bang
            )),
        ),

        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::GreaterThan,
                ..
            })],
            Some((end, '>')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::RightShift
            )),
        ),
        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::RightShift,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::RightShiftEqual
            )),
        ),
        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::GreaterThan,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::GreaterEqual
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '>')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::GreaterThan
            )),
        ),

        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::LessThan,
                ..
            })],
            Some((end, '<')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::LeftShift
            )),
        ),
        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::LeftShift,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::LeftShiftEqual
            )),
        ),
        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::LessThan,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::LessEqual
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '<')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::LessThan
            )),
        ),

        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Ampersand,
                ..
            })],
            Some((end, '&')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::AmpersandAmpersand
            )),
        ),
        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Ampersand,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::AmpersandEqual
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '&')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Ampersand
            )),
        ),

        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Pipe,
                ..
            })],
            Some((end, '|')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::PipePipe
            )),
        ),
        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Pipe,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::PipeEqual
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '|')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Pipe
            )),
        ),
        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Caret,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::CaretEqual
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '^')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Caret
            )),
        ),

        ([TokenOrLexeme::Lexeme(cur, '~')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Tilde
            )),
        ),

        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Plus,
                ..
            })],
            Some((end, '+')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::PlusPlus
            )),
        ),
        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Plus,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::PlusEqual
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '+')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Plus
            )),
        ),

        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Minus,
                ..
            })],
            Some((end, '-')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::MinusMinus
            )),
        ),
        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Minus,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::MinusEqual
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '-')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Minus
            )),
        ),

        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Star,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::StarEqual
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '*')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Star
            )),
        ),

        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::Slash,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::SlashEqual
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '/')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::Slash
            )),
        ),

        (
            [TokenOrLexeme::Token(Token {
                span: start,
                kind: TokenKind::PercentSign,
                ..
            })],
            Some((end, '=')),
        ) => LexOperation::ShiftReduce(
            2,
            token!(Token::new(
                Span::new(start.start, end.increment_column()),
                TokenKind::PercentEqual
            )),
        ),
        ([TokenOrLexeme::Lexeme(cur, '%')], _) => LexOperation::Reduce(
            1,
            token!(Token::new(
                Span::new(*cur, cur.increment_column()),
                TokenKind::PercentSign
            )),
        ),

        (
            [TokenOrLexeme::Lexeme(start, '\''), TokenOrLexeme::Lexeme(_, c), TokenOrLexeme::Lexeme(end, '\'')],
            _,
        ) if c.is_ascii() => {
            let start_idx = start.index + 1;
            let end_idx = end.index;
            let data = &source[start_idx..end_idx];

            LexOperation::Reduce(
                3,
                token!(Token::with_data(
                    Span::new(*start, end.increment_column()),
                    data,
                    TokenKind::CharacterConstant
                )),
            )
        }
        ([TokenOrLexeme::Lexeme(_, '\'')], Some((cur, l))) if l.is_ascii() || l == '\\' => {
            LexOperation::Shift(lexeme!(cur, l))
        }
        (
            [TokenOrLexeme::Lexeme(start, '\''), TokenOrLexeme::Lexeme(_, '\\'), TokenOrLexeme::Lexeme(_, c)],
            Some((end, '\'')),
        ) if c.is_ascii() => {
            let start_idx = start.index + 1;
            let end_idx = end.index;
            let data = &source[start_idx..end_idx];

            LexOperation::ShiftReduce(
                4,
                token!(Token::with_data(
                    Span::new(*start, end.increment_column()),
                    data,
                    TokenKind::CharacterConstant
                )),
            )
        }
        ([TokenOrLexeme::Lexeme(start, '\''), TokenOrLexeme::Lexeme(_, c)], Some((end, '\'')))
            if c.is_ascii() =>
        {
            let start_idx = start.index + 1;
            let end_idx = end.index;
            let data = &source[start_idx..end_idx];

            LexOperation::ShiftReduce(
                3,
                token!(Token::with_data(
                    Span::new(*start, end.increment_column()),
                    data,
                    TokenKind::CharacterConstant
                )),
            )
        }

        ([TokenOrLexeme::Lexeme(_, '\"'), TokenOrLexeme::Lexeme(_, '\\')], Some((cur, '\"'))) => {
            LexOperation::Shift(lexeme!(cur, '\"'))
        }
        ([TokenOrLexeme::Lexeme(_, '\"'), TokenOrLexeme::Lexeme(cur, '\\')], Some((_, c))) => {
            LexOperation::ShiftReduce(2, lexeme!(*cur, to_ascii_escaped_char(c).unwrap()))
        }
        ([TokenOrLexeme::Lexeme(start, '\"'), inner @ ..], Some((end, '\"'))) => {
            let token_cnt = inner.len() + 2;

            let start_idx = start.index + 1;
            let end_idx = end.index;
            let data = &source[start_idx..end_idx];

            LexOperation::ShiftReduce(
                token_cnt,
                token!(Token::with_data(
                    Span::new(*start, end.increment_column()),
                    data,
                    TokenKind::StringLiteral
                )),
            )
        }
        ([TokenOrLexeme::Lexeme(_, '\"'), ..], Some((cur, c))) => {
            LexOperation::Shift(lexeme!(cur, c))
        }

        ([TokenOrLexeme::Lexeme(cur, c)], _) if c.is_digit(10) => {
            let start = cur.index;
            let end = start + 1;
            let data = &source[start..end];

            LexOperation::Reduce(
                1,
                token!(Token::with_data(
                    Span::new(*cur, cur.increment_column()),
                    data,
                    TokenKind::IntegerConstant
                )),
            )
        }
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::IntegerConstant,
                ..
            })],
            Some((cur, c)),
        ) if c.is_digit(10) => {
            let start = span.start.index;
            let end = cur.index + 1;
            let data = &source[start..end];

            LexOperation::ShiftReduce(
                2,
                token!(Token::with_data(
                    Span::new(span.start, cur.increment_column()),
                    data,
                    TokenKind::IntegerConstant,
                )),
            )
        }

        // Identifiers
        ([contents @ ..], Some((cur, c)))
            if matches_rules(contents, lexeme_is_identifier_ascii())
                && matches_rules(&[lexeme!(cur, c)], lexeme_is_identifier_ascii()) =>
        {
            LexOperation::Shift(lexeme!(cur, c))
        }

        // if lookahead doesn't match an identifier reduce
        ([TokenOrLexeme::Lexeme(start, start_c), contents @ ..], Some((cur, l)))
            if matches_rules(contents, lexeme_is_identifier_ascii())
                && matches_rules(
                    &[TokenOrLexeme::Lexeme(*start, *start_c)],
                    lexeme_is_identifier_ascii(),
                )
                && !matches_rules(&[lexeme!(cur, l)], lexeme_is_identifier_ascii()) =>
        {
            let token_cnt = contents.len() + 1;
            // lookahead's cursor is the non-inclusive end.
            let end = cur;
            let data = &source[start.index..end.index];

            LexOperation::Reduce(
                token_cnt,
                token!(Token::with_data(
                    Span::new(*start, end),
                    data,
                    TokenKind::Identifier
                )),
            )
        }
        // end of input
        (
            [TokenOrLexeme::Lexeme(start, start_c), contents @ .., TokenOrLexeme::Lexeme(end, end_c)],
            None,
        ) if matches_rules(contents, lexeme_is_identifier_ascii())
            && matches_rules(
                &[TokenOrLexeme::Lexeme(*start, *start_c)],
                lexeme_is_identifier_ascii(),
            )
            && matches_rules(
                &[TokenOrLexeme::Lexeme(*end, *end_c)],
                lexeme_is_identifier_ascii(),
            ) =>
        {
            // increment column to extend past the end of input.
            let end = end.increment_column();
            let data = &source[start.index..end.index];
            let token_cnt = contents.len() + 2;
            // lookahead's cursor is the non-inclusive end.

            LexOperation::Reduce(
                token_cnt,
                token!(Token::with_data(
                    Span::new(*start, end),
                    data,
                    TokenKind::Identifier
                )),
            )
        }

        // Type Keywords
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("auto"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Auto))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("break"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Break))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("case"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Case))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("char"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Char))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("const"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Const))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("continue"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Continue))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("default"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Default))),

        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("do"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Do))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("double"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Double))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("else"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Else))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("enum"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Enum))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("extern"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Extern))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("float"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Float))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("for"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::For))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("goto"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Goto))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("if"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::If))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("int"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Int))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("long"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Long))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("register"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Register))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("return"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Return))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("short"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Short))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("signed"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Signed))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("sizeof"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::SizeOf))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("static"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Static))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("struct"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Struct))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("switch"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Switch))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("typedef"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::TypeDef))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("union"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Union))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("unsigned"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Unsigned))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("void"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Void))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("volatile"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::Volatile))),
        (
            [TokenOrLexeme::Token(Token {
                span,
                kind: TokenKind::Identifier,
                data: Some("while"),
            })],
            _,
        ) => LexOperation::Reduce(1, token!(Token::new(*span, TokenKind::While))),

        ([TokenOrLexeme::Token(_)], _) | ([.., TokenOrLexeme::Token(_)], _) => {
            LexOperation::NoFurtherRefinement
        }
        ([.., TokenOrLexeme::Lexeme(_, c)], _) if c.is_whitespace() => match *c {
            '\n' => LexOperation::Advance(1, AdvanceOperation::IncrementLine),
            _ => LexOperation::Advance(1, AdvanceOperation::IncrementColumn),
        },

        _ => LexOperation::Err("No rules matched with unpaired lexemes.".to_string()),
    }
}

enum ScanState<T, E> {
    Ok(T),
    Err(E),
    Done,
}

/// Scanner takes a string representing lox source and attempts to convert the
/// source into a vector of either Tokens or lexical errors.
pub struct Scanner<'a> {
    source: &'a str,
    iter: core::iter::Peekable<core::str::Chars<'a>>,
    cursor: Cursor,
    stack: LexerStack<'a, STACK_SIZE>,
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
            source,
            iter: source.chars().peekable(),
            cursor: Cursor::default(),
            stack,
            end,
        }
    }

    fn is_empty(&self) -> bool {
        let index = self.cursor.index;
        index >= self.end
    }

    fn scan_token_from(&mut self) -> ScanState<Token<'a>, String> {
        use ScanState::*;

        if self.iter.peek().is_none() {
            ScanState::Done
        } else {
            let mut lookahead = self.iter.peek().copied();
            loop {
                let stack = self.stack.as_ref();
                let postional_char = lookahead.map(|c| (self.cursor, c));
                let op = stack_eval_to_token(self.source, stack, postional_char);

                match op {
                    LexOperation::Shift(TokenOrLexeme::Lexeme(cur, '\n')) => {
                        self.stack.push_mut(lexeme!(cur, '\n'));
                        lookahead = consume_and_peek_from_iter(&mut self.iter);
                    }
                    LexOperation::Shift(next_val) => {
                        self.stack.push_mut(next_val);
                        lookahead = consume_and_peek_from_iter(&mut self.iter);
                        self.cursor.increment_column_mut();
                    }
                    LexOperation::ShiftReduce(by, TokenOrLexeme::Token(to_token)) => {
                        lookahead = consume_and_peek_from_iter(&mut self.iter);
                        // pop n elements off the stack
                        for _ in 0..by {
                            self.stack.pop_mut();
                        }

                        self.stack.push_mut(TokenOrLexeme::Token(to_token));
                        self.cursor.increment_column_mut();
                    }

                    LexOperation::ShiftReduce(by, TokenOrLexeme::Lexeme(cur, next_val)) => {
                        lookahead = consume_and_peek_from_iter(&mut self.iter);
                        for _ in 0..by {
                            self.stack.pop_mut();
                        }
                        self.stack.push_mut(lexeme!(cur, next_val));
                        self.cursor.increment_column_mut();
                    }
                    LexOperation::Advance(by, AdvanceOperation::IncrementLine) => {
                        // pop the newline off the stack.
                        for _ in 0..by {
                            self.stack.pop_mut();
                        }

                        self.cursor.increment_line_mut();
                    }
                    // this will only occur with whitespace
                    LexOperation::Advance(by, AdvanceOperation::IncrementColumn) => {
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
                        Some(TokenOrLexeme::Token(tok)) => return ScanState::Ok(tok),
                        _ => return Err(format!("invalid token at {}", &self.cursor)),
                    },

                    LexOperation::Err(e) => {
                        return ScanState::Err(format!("{} at {}", e, &self.cursor))
                    }
                }
            }
        }
    }
}

impl<'a> IntoIterator for Scanner<'a> {
    type Item = Result<Token<'a>, String>;
    type IntoIter = ScannerIntoIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        ScannerIntoIterator { scanner: self }
    }
}

pub struct ScannerIntoIterator<'a> {
    scanner: Scanner<'a>,
}

impl<'a> Iterator for ScannerIntoIterator<'a> {
    type Item = Result<Token<'a>, String>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.scanner.is_empty() {
            None
        } else {
            let next = self.scanner.scan_token_from();
            match next {
                ScanState::Done => None,
                ScanState::Ok(token) => Some(Ok(token)),
                ScanState::Err(e) => Some(Err(e)),
            }
        }
    }
}

/// lex all tokens into a a result vector. This should almost always be used directly as an iterator over
/// the scanner.
///
/// # Notes
/// This requires a needless collect to prevent a stack error.
#[allow(clippy::needless_collect, unused)]
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
    fn should_generate_sub_str_from_token() {
        let input = "unsigned int";

        let span = Span::new(Cursor::new(9, 9, 0), Cursor::new(12, 12, 0));
        let token = Token::new(span, TokenKind::Int);

        assert_eq!(Some("int"), token.str_from_input(input))
    }

    #[test]
    fn should_scan_single_token() {
        let inputs = [(0, "{"), (1, " {"), (1, " { ")];

        for (pos, input) in inputs.iter() {
            let mut scanner = Scanner::new(input).into_iter();

            let start = *pos;
            let end = start + 1;

            assert_eq!(
                Some(Ok(Token::new(
                    Span::new(Cursor::new(start, start, 1), Cursor::new(end, end, 1)),
                    TokenKind::LeftBrace
                ))),
                scanner.next()
            )
        }
    }

    #[test]
    fn should_scan_compound_token() {
        let input_expected = [
            (
                [(0, 1, "<"), (1, 2, " <"), (1, 2, " < ")],
                TokenKind::LessThan,
            ),
            (
                [(0, 2, "<="), (1, 3, " <="), (1, 3, " <= ")],
                TokenKind::LessEqual,
            ),
        ];

        for (inputs, expected_kind) in input_expected {
            for (start, end, input) in inputs {
                let mut scanner = Scanner::new(input).into_iter();

                assert_eq!(
                    Some(Ok(Token::new(
                        Span::new(Cursor::new(start, start, 1), Cursor::new(end, end, 1)),
                        expected_kind
                    ))),
                    scanner.next()
                )
            }
        }
    }

    #[test]
    fn should_scan_digit_token() {
        let input_expected = [
            ([(0, 1, "1"), (1, 2, " 1"), (1, 2, " 1 ")], "1"),
            ([(0, 3, "123"), (1, 4, " 123"), (1, 4, " 123 ")], "123"),
        ];

        for (inputs, data) in input_expected {
            for (start, end, input) in inputs {
                let mut scanner = Scanner::new(input).into_iter();

                assert_eq!(
                    Some(Ok(Token::with_data(
                        Span::new(Cursor::new(start, start, 1), Cursor::new(end, end, 1)),
                        data,
                        TokenKind::IntegerConstant
                    ))),
                    scanner.next()
                )
            }
        }
    }

    #[test]
    fn should_scan_char_literals() {
        let inputs = [
            (0, 3, "\'a\'", "a"),
            (1, 4, " \'a\'", "a"),
            (1, 4, " \'a\' ", "a"),
            (0, 3, "\'\t\'", "\t"),
            (1, 4, " \'\t\'", "\t"),
            (0, 3, "\'\t\' ", "\t"),
        ];

        for (start, end, input, data) in inputs {
            let mut scanner = Scanner::new(input).into_iter();

            assert_eq!(
                Some(Ok(Token::with_data(
                    Span::new(Cursor::new(start, start, 1), Cursor::new(end, end, 1)),
                    data,
                    TokenKind::CharacterConstant
                ))),
                scanner.next()
            )
        }
    }

    #[test]
    fn should_scan_string_literals() {
        let input_expected = [
            (0, 7, "\"hello\"", "hello"),
            (1, 8, " \"hello\"", "hello"),
            (1, 8, " \"hello\" ", "hello"),
            (0, 9, "\"hello\\n\"", "hello\\n"),
        ];

        for (start, end, input, expected_data) in input_expected {
            let mut scanner = Scanner::new(input).into_iter();

            assert_eq!(
                Some(Ok(Token::with_data(
                    Span::new(Cursor::new(start, start, 1), Cursor::new(end, end, 1)),
                    expected_data,
                    TokenKind::StringLiteral
                ))),
                scanner.next()
            )
        }
    }

    #[test]
    fn should_scan_identifier() {
        let input_expected = [
            (0, 4, "test", "test"),
            (1, 5, " test", "test"),
            (1, 5, " test ", "test"),
        ];

        for (start, end, input, expected_data) in input_expected {
            let mut scanner = Scanner::new(input).into_iter();

            assert_eq!(
                Some(Ok(Token::with_data(
                    Span::new(Cursor::new(start, start, 1), Cursor::new(end, end, 1)),
                    expected_data,
                    TokenKind::Identifier
                ))),
                scanner.next()
            )
        }
    }

    #[test]
    fn should_scan_keywords() {
        let input_expected = [(0, 3, "for"), (1, 4, " for"), (1, 4, " for ")];

        for (start, end, input) in input_expected {
            let mut scanner = Scanner::new(input).into_iter();

            assert_eq!(
                Some(Ok(Token::new(
                    Span::new(Cursor::new(start, start, 1), Cursor::new(end, end, 1)),
                    TokenKind::For
                ))),
                scanner.next()
            )
        }
    }

    #[test]
    fn should_scan_multiple_tokens() {
        let input = "{ 1 + 2; }";
        let res = lex(input);

        let expected: Result<Vec<_>, _> = Ok(vec![
            Token::new(
                Span::new(Cursor::new(0, 0, 1), Cursor::new(1, 1, 1)),
                TokenKind::LeftBrace,
            ),
            Token::with_data(
                Span::new(Cursor::new(2, 2, 1), Cursor::new(3, 3, 1)),
                "1",
                TokenKind::IntegerConstant,
            ),
            Token::new(
                Span::new(Cursor::new(4, 4, 1), Cursor::new(5, 5, 1)),
                TokenKind::Plus,
            ),
            Token::with_data(
                Span::new(Cursor::new(6, 6, 1), Cursor::new(7, 7, 1)),
                "2",
                TokenKind::IntegerConstant,
            ),
            Token::new(
                Span::new(Cursor::new(7, 7, 1), Cursor::new(8, 8, 1)),
                TokenKind::SemiColon,
            ),
            Token::new(
                Span::new(Cursor::new(9, 9, 1), Cursor::new(10, 10, 1)),
                TokenKind::RightBrace,
            ),
        ]);

        assert_eq!(expected, res)
    }

    #[test]
    fn should_format_span_as_expected() {
        let span = Span::new(Cursor::new(9, 9, 0), Cursor::new(12, 12, 1));

        assert_eq!(
            "(line: 0, column: 9)..(line: 1, column: 12)",
            format!("{}", span)
        )
    }
}
