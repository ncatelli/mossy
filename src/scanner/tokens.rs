/// Token represents any valid token in the grammar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Token {
    PLUS,
    MINUS,
    STAR,
    SLASH,

    // Whitespace
    SPACE,
    TAB,
    NEWLINE,

    // literals
    INTLITERAL(u8),
}
