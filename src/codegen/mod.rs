use crate::ast;

pub mod allocator;
pub mod machine;
mod register;

/// CodeGenerationErr represents an error stemming from the CodeGenerator's
/// `generate` method, capturing any potential point of breakdown withing the
/// code generation process.
#[derive(Clone, PartialEq)]
pub enum CodeGenerationErr {
    Unspecified(String),
}

impl std::fmt::Debug for CodeGenerationErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CodeGenerationErr::Unspecified(e) => {
                write!(f, "unspecified code generation err: {}", e)
            }
        }
    }
}

/// CodeGenerator defines the generate method, returning a string representation
/// of all generated instructions or an error.
pub trait CodeGenerator {
    fn generate(self, input: ast::StmtNode) -> Result<Vec<String>, CodeGenerationErr>;
}

/// TargetCodeGenerator implmements CodeGenerator, storing code context,
/// register allocator and other metadata for a specific architecture.
pub struct TargetCodeGenerator<T, A>
where
    T: machine::arch::TargetArchitecture,
    A: allocator::Allocator,
{
    target_architecture: std::marker::PhantomData<T>,
    allocator: A,
    context: Vec<String>,
}

impl<T, R> TargetCodeGenerator<T, R>
where
    T: machine::arch::TargetArchitecture,
    R: allocator::Allocator + Default,
{
    pub fn new() -> Self {
        Self::default()
    }
}

impl<T, R> Default for TargetCodeGenerator<T, R>
where
    T: machine::arch::TargetArchitecture,
    R: allocator::Allocator + Default,
{
    fn default() -> Self {
        Self {
            target_architecture: std::marker::PhantomData,
            allocator: <R>::default(),
            context: Vec::new(),
        }
    }
}
