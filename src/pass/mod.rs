pub mod type_pass;

pub trait TreePass<I, O> {
    type Error;

    fn analyze(&mut self, input: I) -> Result<O, Self::Error>;
}

/// CodeGenerator defines the generate method, returning a string representation
/// of all generated instructions or an error.
pub trait CodeGenerator<I> {
    type Error;

    fn generate(&self, input: I) -> Result<Vec<String>, Self::Error>;
}
