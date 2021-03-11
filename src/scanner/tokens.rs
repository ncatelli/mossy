/// Token represents any valid token in the grammar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Token {
    PLUS,
    MINUS,
    STAR,
    SLASH,

    // literals
    INTLITERAL(u8),

    // EOF
    EOF,
}
