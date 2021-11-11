pub mod machine;
mod register;
pub mod type_pass;

/// CodeGenerationErr represents an error stemming from the CodeGenerator's
/// `generate` method, capturing any potential point of breakdown withing the
/// code generation process.
#[derive(Clone, PartialEq)]
pub enum CodeGenerationErr {
    UndefinedReference(String),
    Unspecified(String),
}

impl std::fmt::Debug for CodeGenerationErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

pub trait TreePass<I, O> {
    type Error;

    fn analyze(&mut self, input: I) -> Result<O, Self::Error>;
}

/// CodeGenerator defines the generate method, returning a string representation
/// of all generated instructions or an error.
pub trait CodeGenerator<S, I> {
    type Error;

    fn generate(&self, symboltable: &mut S, input: I) -> Result<Vec<String>, Self::Error>;
}
