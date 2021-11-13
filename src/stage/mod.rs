pub mod codegen;
pub mod type_check;

/// TreePass represents a transformation pass on the ADT. Taking an input and
/// Output type for the pass.
pub trait CompilationStage<I, O> {
    type Error;

    fn apply(&mut self, input: I) -> Result<O, Self::Error>;
}
