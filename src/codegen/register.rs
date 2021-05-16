/// Register represents a string representable register that can be used both by
/// allocators and by code generation.
#[derive(Debug, Clone, Copy)]
pub struct Register {
    repr: &'static str,
}

impl Register {
    /// instantiates a register with the str representation passed as `repr`.
    pub fn new(repr: &'static str) -> Self {
        Self { repr }
    }

    /// returns the string representation of the register.
    pub fn id(&self) -> &'static str {
        self.repr
    }
}

impl From<&'static str> for Register {
    fn from(repr: &'static str) -> Self {
        Self::new(repr)
    }
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.repr)
    }
}
