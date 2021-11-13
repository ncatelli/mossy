pub mod codegen;
pub mod type_pass;

/// TreePass represents a transformation pass on the ADT. Taking an input and
/// Output type for the pass.
pub trait CompilationStage<I, O> {
    type Error;

    fn analyze(&mut self, input: I) -> Result<O, Self::Error>;
}
