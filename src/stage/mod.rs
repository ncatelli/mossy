use core::marker::PhantomData;

#[macro_use]
pub mod type_check;

#[macro_use]
pub mod codegen;

/// CompilationStage represents a transformation pass on the ADT. Taking an
/// `Input` and `Output` type for the stage.
pub trait CompilationStage<I, O, E> {
    fn apply(&mut self, input: I) -> Result<O, E>;

    fn and_then<'a, F, Next, O2>(self, next: F) -> BoxedCompilationStage<'a, I, O2, E>
    where
        Self: Sized + 'a,
        I: 'a,
        O: 'a,
        O2: 'a,
        E: 'a,
        Next: CompilationStage<O, O2, E> + 'a,
        F: Fn() -> Next,
    {
        BoxedCompilationStage::new(AndThen::new(self, next()))
    }
}

impl<F, I, O, E> CompilationStage<I, O, E> for F
where
    F: Fn(I) -> Result<O, E>,
{
    fn apply(&mut self, input: I) -> Result<O, E> {
        self(input)
    }
}

/// Provides a compilation stage that is provided on heap.
pub struct BoxedCompilationStage<'a, I, O, E> {
    stage: Box<dyn CompilationStage<I, O, E> + 'a>,
}

impl<'a, I, O, E> BoxedCompilationStage<'a, I, O, E> {
    pub fn new<S>(stage: S) -> Self
    where
        S: CompilationStage<I, O, E> + 'a,
    {
        BoxedCompilationStage {
            stage: Box::new(stage),
        }
    }
}

impl<'a, I, O, E> CompilationStage<I, O, E> for BoxedCompilationStage<'a, I, O, E> {
    fn apply(&mut self, input: I) -> Result<O, E> {
        self.stage.apply(input)
    }
}

/// Joins two compilation stages, executing them in sequential order. This will
/// execute `S1` then `S2` if `S1` returns an `Ok` response. otherwise a
/// failure in any stage will result in an error return.
#[derive(Debug)]
pub struct AndThen<S1, S2, S1I, S1O, S2O, E> {
    input: PhantomData<S1I>,
    output_one: PhantomData<S1O>,
    output_two: PhantomData<S2O>,
    error_type: PhantomData<E>,
    stage1: S1,
    stage2: S2,
}

impl<S1, S2, S1I, S1O, S2O, E> AndThen<S1, S2, S1I, S1O, S2O, E> {
    pub fn new(stage1: S1, stage2: S2) -> Self {
        Self {
            input: PhantomData,
            output_one: PhantomData,
            output_two: PhantomData,
            error_type: PhantomData,
            stage1,
            stage2,
        }
    }
}

impl<S1, S2, S1I, S1O, S2O, E> CompilationStage<S1I, S2O, E> for AndThen<S1, S2, S1I, S1O, S2O, E>
where
    S1: CompilationStage<S1I, S1O, E>,
    S2: CompilationStage<S1O, S2O, E>,
{
    fn apply(&mut self, input: S1I) -> Result<S2O, E> {
        self.stage1
            .apply(input)
            .and_then(|s1_output| self.stage2.apply(s1_output))
    }
}
