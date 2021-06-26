use crate::codegen::machine::arch::TargetArchitecture;

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

type BlockId = usize;

#[derive(Debug, Clone, PartialEq)]
struct Block<T> {
    id: BlockId,
    entry: Option<BlockId>,
    inner: T,
    exit_cond_true: Option<BlockId>,
    exit_cond_false: Option<BlockId>,
}

impl<T> Block<T> {
    fn new(
        id: BlockId,
        entry: Option<BlockId>,
        inner: T,
        exit_cond_true: Option<BlockId>,
        exit_cond_false: Option<BlockId>,
    ) -> Self {
        Self {
            id,
            entry,
            inner,
            exit_cond_true,
            exit_cond_false,
        }
    }
}

impl<T> Block<T>
where
    T: Default,
{
    fn derive_child(self) -> (Self, Self) {
        let mut parent = self;
        let parent_id = parent.id;
        let child_block = Self::new(
            generate_next_block_id(),
            Some(parent_id),
            T::default(),
            None,
            None,
        );
        let child_id = child_block.id;
        parent.exit_cond_true = Some(child_id);

        (parent, child_block)
    }
}

impl<T> Block<Vec<T>> {
    fn prepend(mut self, inner: T) -> Self {
        self.prepend_mut(inner);
        self
    }

    fn prepend_mut(&mut self, inner: T) {
        self.inner.insert(0, inner);
    }

    fn append(mut self, inner: T) -> Self {
        self.append_mut(inner);
        self
    }

    fn append_mut(&mut self, inner: T) {
        self.inner.push(inner);
    }
}

impl<T> Default for Block<T>
where
    T: Default,
{
    fn default() -> Self {
        Self {
            id: 0,
            entry: None,
            inner: T::default(),
            exit_cond_true: None,
            exit_cond_false: None,
        }
    }
}

/// X86_64 represents the x86_64 bit machine target.
#[derive(Clone, Copy)]
pub struct X86_64;

mod register;
use register::SizedGeneralPurpose;

impl TargetArchitecture for X86_64 {}

use crate::ast;
use crate::ast::ExprNode;

impl crate::codegen::CodeGenerator<(), ast::CompoundStmts> for X86_64 {
    fn generate(
        &self,
        _symboltable: &mut (),
        input: ast::CompoundStmts,
    ) -> Result<Vec<String>, crate::codegen::CodeGenerationErr> {
        let block = Block::default();
        input
            .emit(block)
            .map(|blocks| {
                blocks
                    .into_iter()
                    // TODO: Remove this, block should generate this.
                    .map(|block| {
                        let id = block.id;
                        block.prepend(format!("L{}:\n", id))
                    })
                    .flat_map(|block| block.inner)
                    .collect::<Vec<String>>()
            })
            .map_err(crate::codegen::CodeGenerationErr::Unspecified)
    }
}

fn preamble<'a>() -> impl CodeGenEmitter<'a, Block<Vec<String>>, Block<Vec<String>>> {
    move |input: Block<Vec<String>>| Ok(input.append(CG_PREAMBLE.to_string()))
}

fn postamble<'a>() -> impl CodeGenEmitter<'a, Block<Vec<String>>, [Block<Vec<String>>; 2]> {
    move |input: Block<Vec<String>>| {
        let (parent, child) = input.derive_child();
        Ok([parent, child.append(CG_POSTAMBLE.to_string())])
    }
}

fn label<'a>(block_id: BlockId) -> impl CodeGenEmitter<'a, Block<Vec<String>>, Block<Vec<String>>> {
    move |input: Block<Vec<String>>| Ok(input.append(format!("L{}:\n", block_id)))
}

fn jump<'a>(block_id: BlockId) -> impl CodeGenEmitter<'a, Block<Vec<String>>, Block<Vec<String>>> {
    move |input: Block<Vec<String>>| Ok(input.append(format!("\tjmp\tL{}\n", block_id)))
}

fn with_allocator_pool<'a, P>(
    pool: &'a [P],
) -> impl CodeGenEmitter<'a, Block<Vec<String>>, (&'a [P], Block<Vec<String>>)> {
    move |input: Block<Vec<String>>| Ok((pool, input))
}

/// Represents a common pattern of grouping a general-purpose register pool, a
/// return value general-purpose register and a block.
type AllocatorReturnValueBlock<'a> = (
    &'a [SizedGeneralPurpose],
    &'a SizedGeneralPurpose,
    Block<Vec<String>>,
);

impl<'a> CodeGenEmitter<'a, Block<Vec<String>>, Vec<Block<Vec<String>>>> for ast::CompoundStmts {
    fn emit(&self, block: Block<Vec<String>>) -> EmitResult<'a, Vec<Block<Vec<String>>>> {
        self.inner.iter().try_fold(vec![block], |mut acc, stmt| {
            acc.pop()
                .ok_or_else(|| "Undefined block".to_string())
                .and_then(|last| stmt.emit(last))
                .and_then(|result_blocks| {
                    acc.extend(result_blocks.into_iter());
                    Ok(acc)
                })
        })
    }
}

/// evaulate an statement node.
impl<'a> CodeGenEmitter<'a, Block<Vec<String>>, Vec<Block<Vec<String>>>> for ast::StmtNode {
    fn emit(&self, block: Block<Vec<String>>) -> EmitResult<'a, Vec<Block<Vec<String>>>> {
        match self {
            ast::StmtNode::Declaration(_) => todo!(),
            ast::StmtNode::Assignment(_) => todo!(),
            ast::StmtNode::Expression(expr_stmt) => expr_stmt.emit(block).map(|res| vec![res]),
            ast::StmtNode::If(_) => todo!(),
        }
    }
}

/// evaulate an Expressions statement.
impl<'a> CodeGenEmitter<'a, Block<Vec<String>>, Block<Vec<String>>> for ast::ExpressionStmt {
    fn emit(&self, block: Block<Vec<String>>) -> EmitResult<'a, Block<Vec<String>>> {
        with_allocator_pool(&register::GPRegisters)
            .and_then(AllocateRegisterWithPool::new(
                |(pool, ret_val, block): AllocatorReturnValueBlock| {
                    self.inner.emit((&pool[..], ret_val, block))
                },
            ))
            .emit(block)
    }
}

/// evaulate an expression node.
impl<'a> CodeGenEmitter<'a, AllocatorReturnValueBlock<'a>, Block<Vec<String>>> for ast::ExprNode {
    fn emit(
        &self,
        (pool, ret_val, block): AllocatorReturnValueBlock<'a>,
    ) -> EmitResult<'a, Block<Vec<String>>> {
        match self {
            ExprNode::Primary(ast::Primary::Uint8(val)) => val.emit((ret_val, block)),
            ExprNode::Primary(_) => todo!(),
            ExprNode::Equal(_) => todo!(),
            ExprNode::NotEqual(_) => todo!(),
            ExprNode::LessThan(_) => todo!(),
            ExprNode::GreaterThan(_) => todo!(),
            ExprNode::LessEqual(_) => todo!(),
            ExprNode::GreaterEqual(_) => todo!(),
            ExprNode::Subtraction(_) => todo!(),
            ExprNode::Division(_) => todo!(),
            ExprNode::Addition(add_expr) => add_expr.emit((pool, ret_val, block)),
            ExprNode::Multiplication(_) => todo!(),
        }
    }
}

/// evaluate addition
impl<'a>
    CodeGenEmitter<
        'a,
        (
            &'a [SizedGeneralPurpose],
            &'a SizedGeneralPurpose,
            Block<Vec<String>>,
        ),
        Block<Vec<String>>,
    > for ast::AdditionExprNode
{
    fn emit(
        &self,
        (pool, ret_val, block): AllocatorReturnValueBlock,
    ) -> EmitResult<'a, Block<Vec<String>>> {
        self.lhs.emit((pool, ret_val, block)).and_then(|block| {
            AllocateRegisterWithPool::new(
                |(pool, rhs_ret_val, block): AllocatorReturnValueBlock| {
                    self.rhs
                        .emit((&pool[..], rhs_ret_val, block))
                        .map(|b| (*rhs_ret_val, b))
                },
            )
            // capture the return value register.
            .map(|(rhs_ret_val, block)| (*ret_val, rhs_ret_val, block))
            .map(|(lhs_reg, rhs_reg, block)| {
                block.append(format!(
                    "\tadd{}\t{}, {}\n",
                    lhs_reg.operator_suffix(),
                    rhs_reg,
                    lhs_reg
                ))
            })
            .emit((&pool[..], block))
        })
    }
}

/// load a constant into a register.
impl<'a> CodeGenEmitter<'a, (&'a SizedGeneralPurpose, Block<Vec<String>>), Block<Vec<String>>>
    for ast::Uint8
{
    fn emit(
        &self,
        (ret_val, block): (&'a SizedGeneralPurpose, Block<Vec<String>>),
    ) -> EmitResult<'a, Block<Vec<String>>> {
        let constant = self.0;
        Ok(block.append(format!(
            "\tmov{}\t${}, {}\n",
            ret_val.operator_suffix(),
            constant,
            ret_val
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reset_block_id_counter(reset_value: usize) {
        BlockIdCounter.store(reset_value, std::sync::atomic::Ordering::SeqCst)
    }

    macro_rules! gen_test_block {
        () => {
            Block::new(generate_next_block_id(), None, vec![], None, None)
        };
        ($inner:expr) => {
            Block::new(generate_next_block_id(), None, $inner, None, None)
        };
        ($inner:expr, $child:expr) => {
            Block::new(generate_next_block_id(), None, $inner, Some($child), None)
        };
    }

    #[test]
    fn should_generate_expected_preamble_block() {
        reset_block_id_counter(0);

        assert_eq!(
            Ok(gen_test_block!(vec![CG_PREAMBLE.to_string()])),
            preamble().emit(Block::default())
        );
    }

    #[test]
    fn should_generate_expected_postamble_block() {
        // Block is defaulting to 0, assume Reset counter has incremented once.
        reset_block_id_counter(1);
        assert_eq!(
            Ok([
                Block::new(0, None, vec![], Some(1), None),
                Block::new(1, Some(0), vec![CG_POSTAMBLE.to_string()], None, None),
            ]),
            postamble().emit(Block::default())
        );
    }

    #[test]
    fn should_be_able_to_compose_generators_of_matching_input_output_types() {
        reset_block_id_counter(1);

        assert_eq!(
            Ok([
                Block::new(0, None, vec![CG_PREAMBLE.to_string()], Some(1), None),
                Block::new(1, Some(0), vec![CG_POSTAMBLE.to_string()], None, None),
            ]),
            preamble().and_then(postamble()).emit(Block::default())
        );
    }

    #[test]
    fn should_generate_8bit_mov_to_register_from_constant_expr() {
        use crate::ast::*;
        use crate::codegen::machine::arch::x86_64::register;

        reset_block_id_counter(0);
        assert_eq!(
            Ok(Block::new(
                0,
                None,
                vec!["\tmovq\t$5, %r15\n".to_string()],
                None,
                None
            )),
            with_allocator_pool(&register::GPRegisters[..])
                .and_then(AllocateRegisterWithPool::new(ExprNode::Primary(
                    Primary::Uint8(Uint8(5))
                )))
                .emit(Block::default())
        );
    }

    #[test]
    fn should_generate_8bit_add_to_register_from_constant_expr() {
        use crate::ast::*;

        reset_block_id_counter(0);
        assert_eq!(
            Ok(Block::new(
                0,
                None,
                vec![
                    "\tmovq\t$1, %r15\n",
                    "\tmovq\t$2, %r14\n",
                    "\taddq\t%r14, %r15\n"
                ]
                .iter()
                .map(|s| s.to_string())
                .collect(),
                None,
                None
            )),
            with_allocator_pool(&register::GPRegisters[..])
                .and_then(AllocateRegisterWithPool::new(ExprNode::Addition(
                    AdditionExprNode::new(
                        Box::new(ExprNode::Primary(Primary::Uint8(Uint8(1)))),
                        Box::new(ExprNode::Primary(Primary::Uint8(Uint8(2)))),
                    )
                )))
                .emit(Block::default())
        );
    }
}
