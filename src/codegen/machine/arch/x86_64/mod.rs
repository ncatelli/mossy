/// Defines a constant preamble to be prepended to any compiled binaries.
pub const CG_PREAMBLE: &str = "\t.text
.LC0:
    .string \"%d\\n\"
printint:
    pushq   %rbp
    movq    %rsp, %rbp
    subq    $16, %rsp
    movl    %edi, -4(%rbp)
    movl    -4(%rbp), %eax
    movl    %eax, %esi
    leaq	.LC0(%rip), %rdi
    movl	$0, %eax
    call	printf@PLT
    nop
    leave
    ret
	
    .globl  main
    .type   main, @function
main:
    pushq   %rbp
    movq	%rsp, %rbp
    jmp     L0\n";

/// Defines a constant postamble to be appended to any compiled binaries.
pub const CG_POSTAMBLE: &str = "\tjmp\tpostamble
postamble:
    movl	$0, %eax
    popq	%rbp
    ret\n";

static BlockIdCounter: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn generate_next_block_id() -> usize {
    BlockIdCounter.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
}

type EmitResult<'a, T> = Result<T, String>;

// combinators

#[derive(Debug)]
struct Map<E, F, A, B, C> {
    input: std::marker::PhantomData<A>,
    output_one: std::marker::PhantomData<B>,
    output_two: std::marker::PhantomData<C>,
    emitter: E,
    map_fn: F,
}

impl<'a, E, F, A, B, C> Map<E, F, A, B, C> {
    pub fn new(emitter: E, map_fn: F) -> Self {
        Self {
            input: std::marker::PhantomData,
            output_one: std::marker::PhantomData,
            output_two: std::marker::PhantomData,
            emitter,
            map_fn,
        }
    }
}

impl<'a, E, F, A, B, C> CodeGenEmitter<'a, A, C> for Map<E, F, A, B, C>
where
    E: CodeGenEmitter<'a, A, B>,
    F: Fn(B) -> C + 'a,
{
    fn emit(&self, input: A) -> EmitResult<'a, C> {
        self.emitter.emit(input).map(|res| (self.map_fn)(res))
    }
}

#[derive(Debug)]
pub struct AndThen<E1, E2, A, B, C> {
    input: std::marker::PhantomData<A>,
    output_one: std::marker::PhantomData<B>,
    output_two: std::marker::PhantomData<C>,
    emitter1: E1,
    emitter2: E2,
}

impl<'a, E1, E2, A, B, C> AndThen<E1, E2, A, B, C> {
    pub fn new(emitter1: E1, emitter2: E2) -> Self {
        Self {
            input: std::marker::PhantomData,
            output_one: std::marker::PhantomData,
            output_two: std::marker::PhantomData,
            emitter1,
            emitter2,
        }
    }
}

impl<'a, E1, E2, A, B, C> CodeGenEmitter<'a, A, C> for AndThen<E1, E2, A, B, C>
where
    A: 'a,
    E1: CodeGenEmitter<'a, A, B>,
    E2: CodeGenEmitter<'a, B, C>,
{
    fn emit(&self, input: A) -> EmitResult<'a, C> {
        self.emitter1
            .emit(input)
            .and_then(|res| self.emitter2.emit(res))
    }
}

#[derive(Debug)]
pub(crate) struct WithAllocatorPool<'a, P, E, A, B> {
    pool: &'a [P],
    input: std::marker::PhantomData<A>,
    output_one: std::marker::PhantomData<B>,
    emitter: E,
}

impl<'a, P, E, A, B> WithAllocatorPool<'a, P, E, A, B> {
    pub fn new(pool: &'a [P], emitter: E) -> Self {
        Self {
            pool,
            input: std::marker::PhantomData,
            output_one: std::marker::PhantomData,
            emitter,
        }
    }
}

impl<'a, P, E, A, B> CodeGenEmitter<'a, A, B> for WithAllocatorPool<'a, P, E, A, B>
where
    A: 'a,
    E: CodeGenEmitter<'a, (&'a [P], A), B>,
{
    fn emit(&self, input: A) -> EmitResult<'a, B> {
        self.emitter.emit((&self.pool[..], input))
    }
}

#[derive(Debug)]
pub struct AllocateRegister<P, E, A, B> {
    pool: std::marker::PhantomData<P>,
    input: std::marker::PhantomData<A>,
    output_one: std::marker::PhantomData<B>,
    emitter: E,
}

impl<'a, P, E, A, B> AllocateRegister<P, E, A, B> {
    pub fn new(emitter: E) -> Self {
        Self {
            pool: std::marker::PhantomData,
            input: std::marker::PhantomData,
            output_one: std::marker::PhantomData,
            emitter,
        }
    }
}

impl<'a, P, E, A, B> CodeGenEmitter<'a, (&'a [P], A), B> for AllocateRegister<P, E, A, B>
where
    A: 'a,
    E: CodeGenEmitter<'a, (&'a P, A), B>,
{
    fn emit(&self, (pool, input): (&'a [P], A)) -> EmitResult<'a, B> {
        let pool_size = pool.len();
        pool.get(pool_size - 1)
            .ok_or_else(|| "unable to allocate register".to_string())
            .and_then(|reg| self.emitter.emit((reg, input)))
    }
}

#[derive(Debug)]
pub struct AllocateRegisterWithPool<P, E, A, B> {
    pool: std::marker::PhantomData<P>,
    input: std::marker::PhantomData<A>,
    output_one: std::marker::PhantomData<B>,
    emitter: E,
}

impl<'a, P, E, A, B> AllocateRegisterWithPool<P, E, A, B> {
    pub fn new(emitter: E) -> Self {
        Self {
            pool: std::marker::PhantomData,
            input: std::marker::PhantomData,
            output_one: std::marker::PhantomData,
            emitter,
        }
    }
}

impl<'a, P, E, A, B> CodeGenEmitter<'a, (&'a [P], A), B> for AllocateRegisterWithPool<P, E, A, B>
where
    A: 'a,
    E: CodeGenEmitter<'a, (&'a [P], &'a P, A), B>,
{
    fn emit(&self, (pool, input): (&'a [P], A)) -> EmitResult<'a, B> {
        let pool_size = pool.len();
        pool.get(pool_size - 1)
            .ok_or_else(|| "unable to allocate register".to_string())
            .and_then(|reg| self.emitter.emit((&pool[..pool_size - 1], reg, input)))
    }
}

pub(crate) trait CodeGenEmitter<'a, A, B> {
    fn emit(&self, input: A) -> EmitResult<'a, B>;

    fn map<F, C>(self, map_fn: F) -> BoxedCodeGenEmitter<'a, A, C>
    where
        Self: Sized + 'a,
        A: 'a,
        B: 'a,
        C: 'a,
        F: Fn(B) -> C + 'a,
    {
        BoxedCodeGenEmitter::new(Map::new(self, map_fn))
    }

    fn and_then<E2, C>(self, next: E2) -> BoxedCodeGenEmitter<'a, A, C>
    where
        Self: Sized + 'a,
        A: 'a,
        B: 'a,
        C: 'a,
        E2: CodeGenEmitter<'a, B, C> + 'a,
    {
        BoxedCodeGenEmitter::new(AndThen::new(self, next))
    }

    fn with_allocator_pool<P>(self, pool: &'a [P]) -> BoxedCodeGenEmitter<'a, A, B>
    where
        Self: Sized + CodeGenEmitter<'a, (&'a [P], A), B> + 'a,
        A: 'a,
        B: 'a,
    {
        BoxedCodeGenEmitter::new(WithAllocatorPool::new(pool, self))
    }

    fn allocate_register<P, E>(self) -> BoxedCodeGenEmitter<'a, (&'a [P], A), B>
    where
        Self: Sized + CodeGenEmitter<'a, (&'a P, A), B> + 'a,
        A: 'a,
        B: 'a,
    {
        BoxedCodeGenEmitter::new(AllocateRegister::new(self))
    }
}

impl<'a, F, A, B> CodeGenEmitter<'a, A, B> for F
where
    A: 'a,
    F: Fn(A) -> EmitResult<'a, B>,
{
    fn emit(&self, input: A) -> EmitResult<'a, B> {
        self(input)
    }
}

pub(crate) struct BoxedCodeGenEmitter<'a, A, B> {
    emitter: Box<dyn CodeGenEmitter<'a, A, B> + 'a>,
}

impl<'a, A, B> BoxedCodeGenEmitter<'a, A, B> {
    pub fn new<E>(emitter: E) -> Self
    where
        E: CodeGenEmitter<'a, A, B> + 'a,
    {
        BoxedCodeGenEmitter {
            emitter: Box::new(emitter),
        }
    }
}

impl<'a, A, B> CodeGenEmitter<'a, A, B> for BoxedCodeGenEmitter<'a, A, B> {
    fn emit(&self, input: A) -> EmitResult<'a, B> {
        self.emitter.emit(input)
    }
}

pub struct X86_64;

impl crate::codegen::machine::arch::TargetArchitecture for X86_64 {}

use crate::codegen::CodeGenerator;
use crate::{ast, codegen};

impl CodeGenerator<(), ast::CompoundStmts> for X86_64 {
    fn generate(
        &self,
        _symboltable: &mut (),
        _input: ast::CompoundStmts,
    ) -> Result<Vec<String>, codegen::CodeGenerationErr> {
        todo!()
    }
}
