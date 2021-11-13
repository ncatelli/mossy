pub mod machine;
mod register;

/// CodeGenerationErr represents an error stemming from the CodeGenerator's
/// `generate` method, capturing any potential point of breakdown withing the
/// code generation process.
#[derive(Clone, PartialEq)]
pub enum CodeGenerationErr {
    UndefinedReference(String),
    Unspecified(String),
}

impl core::fmt::Debug for CodeGenerationErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            CodeGenerationErr::Unspecified(e) => {
                write!(f, "unspecified code generation err: {}", e)
            }
            CodeGenerationErr::UndefinedReference(identifier) => {
                write!(f, "undefined reference: {}", identifier)
            }
        }
    }
}

/// CodeGenerator defines the generate method, returning a string representation
/// of all generated instructions or an error.
pub trait CodeGenerator<I> {
    type Error;

    fn generate(&self, input: I) -> Result<Vec<String>, Self::Error>;
}
