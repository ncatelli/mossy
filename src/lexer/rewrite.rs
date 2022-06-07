/// Defines the wrapper type for an error returned from Lexing
type LexError = String;

/// Lex returns either a
pub type LexResult = Result<Vec<Token>, LexError>;

/// Provides metadata about the classification of a given Token.
#[derive(Debug)]
pub enum TokenClass {
    Identifier,
    Keywords,
    Constant,
    StringLiteral,
    Operator,
    Separator,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Token {
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
}

impl Token {
    pub fn token_class(&self) -> TokenClass {
        match self {
            Token::Auto
            | Token::Break
            | Token::Case
            | Token::Char
            | Token::Const
            | Token::Continue
            | Token::Default
            | Token::Do
            | Token::Double
            | Token::Else
            | Token::Enum
            | Token::Extern
            | Token::Float
            | Token::For
            | Token::Goto
            | Token::If
            | Token::Int
            | Token::Long
            | Token::Register
            | Token::Return
            | Token::Short
            | Token::Signed
            | Token::SizeOf
            | Token::Static
            | Token::Struct
            | Token::Switch
            | Token::TypeDef
            | Token::Union
            | Token::Unsigned
            | Token::Void
            | Token::Volatile
            | Token::While => TokenClass::Keywords,
        }
    }
}
