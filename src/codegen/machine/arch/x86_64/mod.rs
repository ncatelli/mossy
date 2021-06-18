use crate::codegen::machine::arch::TargetArchitecture;
use crate::codegen::register::Register;
use crate::codegen::CodeGenerationErr;

type BlockId = usize;

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
struct BuildContext<BT> {
    active_block: BlockId,
    blocks: Vec<Block<BT>>,
}

impl<BT> BuildContext<BT>
where
    BT: Default,
{
    pub fn get_active_block_mut(&mut self) -> Option<&mut Block<BT>> {
        self.blocks.get_mut(self.active_block)
    }

    pub fn get_mut(&mut self, block_id: BlockId) -> Option<&mut Block<BT>> {
        self.blocks.get_mut(block_id)
    }

    pub fn derive_child_from_parent(&mut self, parent: BlockId) -> BlockId {
        let new_id = self.blocks.len();
        let child = <Block<BT>>::new(new_id, Some(parent), BT::default(), None, None);
        self.blocks.push(child);

        self.active_block = new_id;
        new_id
    }
}

impl<BT> Default for BuildContext<BT>
where
    BT: Default,
{
    fn default() -> Self {
        Self {
            active_block: 0,
            blocks: vec![<Block<BT>>::default()],
        }
    }
}

/// X86_64 represents the x86_64 bit machine target.
#[derive(Clone, Copy)]
pub struct X86_64;

mod register;
use register::{GPRegisterAllocator, SizedGeneralPurpose};

impl TargetArchitecture for X86_64 {}

/// SymbolTable functions as a tracker for symbols that have been previously
/// declared. For the time being, this only tracks global symbols.
#[derive(Default, Debug, Clone)]
pub struct SymbolTable {
    globals: std::collections::HashSet<String>,
}

impl SymbolTable {
    /// Marks a global variable as having been declared.
    pub fn declare_global(&mut self, identifier: &str) {
        self.globals.insert(identifier.to_string());
    }

    /// Returns a boolian representing if a global variable has already been
    /// declared.
    pub fn has_global(&mut self, identifier: &str) -> bool {
        self.globals.contains(identifier)
    }
}

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

use crate::ast;
use crate::ast::ExprNode;
use crate::codegen;
use crate::codegen::machine;
use crate::codegen::CodeGenerator;

impl CodeGenerator<SymbolTable, ast::CompoundStmts> for X86_64 {
    fn generate(
        &self,
        symboltable: &mut SymbolTable,
        input: ast::CompoundStmts,
    ) -> Result<Vec<String>, codegen::CodeGenerationErr> {
        let mut allocator = GPRegisterAllocator::default();

        let ctx = codegen_statements(
            BuildContext::<Vec<String>>::default(),
            &mut allocator,
            symboltable,
            input,
        )?;

        Ok(ctx
            .blocks
            .into_iter()
            .enumerate()
            .map(|(block_id, block)| (codegen_label(block_id), block))
            .map(|(label, block)| {
                let block_id = block.id;
                let inner = block.inner;
                let (ec_true, ec_false) = (block.exit_cond_true, block.exit_cond_false);
                let inner_and_exit: Vec<String> = match (ec_true, ec_false) {
                    (Some(next), None) if next == block_id + 1 => inner,
                    (Some(next), None) => inner
                        .into_iter()
                        .chain(codegen_jump(next).into_iter())
                        .collect(),
                    _ => inner,
                };

                (label, inner_and_exit)
            })
            .map(|(label, insts)| label.into_iter().chain(insts.into_iter()).collect())
            .collect())
    }
}

/// Returns a vector-wrapped preamble.
pub fn codegen_preamble() -> Vec<String> {
    vec![String::from(machine::arch::x86_64::CG_PREAMBLE)]
}

/// Returns a vector-wrapped binary postamble
pub fn codegen_postamble() -> Vec<String> {
    vec![String::from(machine::arch::x86_64::CG_POSTAMBLE)]
}

fn codegen_statements(
    mut ctx: BuildContext<Vec<String>>,
    allocator: &mut GPRegisterAllocator,
    symboltable: &mut SymbolTable,
    input: ast::CompoundStmts,
) -> Result<BuildContext<Vec<String>>, CodeGenerationErr> {
    let stmts = Vec::<ast::StmtNode>::from(input);

    for stmt in stmts.into_iter() {
        ctx = codegen_statement(ctx, allocator, symboltable, stmt)?
    }

    Ok(ctx)
}

fn codegen_statement(
    mut ctx: BuildContext<Vec<String>>,
    allocator: &mut GPRegisterAllocator,
    symboltable: &mut SymbolTable,
    input: ast::StmtNode,
) -> Result<BuildContext<Vec<String>>, CodeGenerationErr> {
    match input {
        ast::StmtNode::Expression(expr) => allocator.allocate_then(|allocator, ret_val| {
            ctx = codegen_expr(ctx, allocator, ret_val, expr);
            ctx.get_active_block_mut().map(|block| {
                for inst in codegen_printint(ret_val).into_iter() {
                    block.inner.push(inst);
                }
            });
            Ok(ctx)
        }),
        ast::StmtNode::Declaration(identifier) => {
            symboltable.declare_global(&identifier);
            let ctx = codegen_global_symbol(ctx, &identifier);
            Ok(ctx)
        }
        ast::StmtNode::Assignment(identifier, expr) => symboltable
            .has_global(&identifier)
            .then(|| ())
            .map(|_| {
                allocator.allocate_then(|allocator, ret_val| {
                    let expr_ctx = codegen_expr(ctx, allocator, ret_val, expr);
                    codegen_store_global(expr_ctx, ret_val, &identifier)
                })
            })
            .ok_or(CodeGenerationErr::UndefinedReference(identifier)),
        ast::StmtNode::If(cond, true_case, false_case) => codegen_if_statement(
            ctx,
            allocator,
            symboltable,
            cond,
            true_case,
            false_case.map(|stmts| stmts),
        ),
    }
}

fn codegen_if_statement(
    ctx: BuildContext<Vec<String>>,
    allocator: &mut GPRegisterAllocator,
    symboltable: &mut SymbolTable,
    cond: crate::ast::ExprNode,
    true_case: crate::ast::CompoundStmts,
    false_case: Option<crate::ast::CompoundStmts>,
) -> Result<BuildContext<Vec<String>>, CodeGenerationErr> {
    allocator.allocate_then(|allocator, ret_val| {
        let parent_block_id = ctx.active_block;
        let mut cond_ctx = codegen_expr(ctx, allocator, ret_val, cond);
        let exit_block_id = if false_case.is_some() {
            parent_block_id + 3
        } else {
            parent_block_id + 2
        };

        let true_case_block_id = cond_ctx.derive_child_from_parent(parent_block_id);
        cond_ctx
            .get_mut(parent_block_id)
            .map(|parent| parent.exit_cond_true = Some(true_case_block_id));

        let mut tctx = codegen_statements(cond_ctx, allocator, symboltable, true_case)?;
        tctx.get_active_block_mut()
            .map(|block| block.exit_cond_true = Some(exit_block_id));

        let (mut block_ctx, else_block_id) = if let Some(false_case_stmts) = false_case {
            let false_case_block_id = tctx.derive_child_from_parent(parent_block_id);
            tctx.get_mut(parent_block_id)
                .map(|parent| parent.exit_cond_false = Some(false_case_block_id));

            let mut fctx = codegen_statements(tctx, allocator, symboltable, false_case_stmts)?;
            fctx.get_active_block_mut()
                .map(|block| block.exit_cond_true = Some(exit_block_id));
            (fctx, false_case_block_id)
        } else {
            (tctx, exit_block_id)
        };

        // reset parent block for compare.
        block_ctx.active_block = parent_block_id;
        let mut compare_block = codegen_compare_and_jump(
            block_ctx,
            allocator,
            ret_val,
            true_case_block_id,
            else_block_id,
        );

        // generate an exit block
        compare_block.derive_child_from_parent(parent_block_id);

        Ok(compare_block)
    })
}

fn codegen_global_symbol(
    mut ctx: BuildContext<Vec<String>>,
    identifier: &str,
) -> BuildContext<Vec<String>> {
    ctx.get_active_block_mut()
        .map(|block| block.inner.push(format!("\t.comm\t{},1,8\n", identifier)));
    ctx
}

fn codegen_store_global(
    mut ctx: BuildContext<Vec<String>>,
    ret: &mut SizedGeneralPurpose,
    identifier: &str,
) -> BuildContext<Vec<String>> {
    ctx.get_active_block_mut().map(|block| {
        block.inner.push(format!(
            "\tmov{}\t%{}, {}(%rip)\n",
            ret.operator_suffix(),
            ret.id(),
            identifier
        ))
    });
    ctx
}

fn codegen_load_global(
    mut ctx: BuildContext<Vec<String>>,
    ret: &mut SizedGeneralPurpose,
    identifier: &str,
) -> BuildContext<Vec<String>> {
    ctx.get_active_block_mut().map(|block| {
        block.inner.push(format!(
            "\tmov{}\t{}(%rip), %{}\n",
            ret.operator_suffix(),
            identifier,
            ret.id()
        ))
    });
    ctx
}

pub fn codegen_label(block_id: usize) -> Vec<String> {
    vec![format!("L{}:\n", block_id)]
}

pub fn codegen_jump(block_id: usize) -> Vec<String> {
    vec![format!("\tjmp\tL{}\n", block_id)]
}

fn codegen_expr(
    ctx: BuildContext<Vec<String>>,
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    expr: crate::ast::ExprNode,
) -> BuildContext<Vec<String>> {
    use crate::ast::Primary;

    match expr {
        ExprNode::Primary(Primary::Uint8(ast::Uint8(uc))) => codegen_constant_u8(ctx, ret_val, uc),
        ExprNode::Primary(Primary::Identifier(identifier)) => {
            codegen_load_global(ctx, ret_val, &identifier)
        }

        ExprNode::Equal(ast::EqualExprNode { lhs, rhs }) => codegen_compare_and_set(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::Equal,
            lhs,
            rhs,
        ),
        ExprNode::NotEqual(ast::NotEqualExprNode { lhs, rhs }) => codegen_compare_and_set(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::NotEqual,
            lhs,
            rhs,
        ),
        ExprNode::LessThan(ast::LessThanExprNode { lhs, rhs }) => codegen_compare_and_set(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::LessThan,
            lhs,
            rhs,
        ),
        ExprNode::GreaterThan(ast::GreaterThanExprNode { lhs, rhs }) => codegen_compare_and_set(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::GreaterThan,
            lhs,
            rhs,
        ),
        ExprNode::LessEqual(ast::LessEqualExprNode { lhs, rhs }) => codegen_compare_and_set(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::LessEqual,
            lhs,
            rhs,
        ),
        ExprNode::GreaterEqual(ast::GreaterEqualExprNode { lhs, rhs }) => codegen_compare_and_set(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::GreaterEqual,
            lhs,
            rhs,
        ),
        ExprNode::Addition(ast::AdditionExprNode { lhs, rhs }) => {
            codegen_addition(ctx, allocator, ret_val, lhs, rhs)
        }
        ExprNode::Subtraction(ast::SubtractionExprNode { lhs, rhs }) => {
            codegen_subtraction(ctx, allocator, ret_val, lhs, rhs)
        }
        ExprNode::Multiplication(ast::MultiplicationExprNode { lhs, rhs }) => {
            codegen_multiplication(ctx, allocator, ret_val, lhs, rhs)
        }
        ExprNode::Division(ast::DivisionExprNode { lhs, rhs }) => {
            codegen_division(ctx, allocator, ret_val, lhs, rhs)
        }
    }
}

fn codegen_constant_u8(
    mut ctx: BuildContext<Vec<String>>,
    ret_val: &mut SizedGeneralPurpose,
    constant: u8,
) -> BuildContext<Vec<String>> {
    ctx.get_active_block_mut().map(|block| {
        block.inner.push(
            vec![format!(
                "\tmov{}\t${}, {}\n",
                ret_val.operator_suffix(),
                constant,
                ret_val
            )]
            .into_iter()
            .collect(),
        )
    });
    ctx
}

fn codegen_addition(
    ctx: BuildContext<Vec<String>>,
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> BuildContext<Vec<String>> {
    allocator.allocate_then(|allocator, lhs_retval| {
        let lhs_ctx = codegen_expr(ctx, allocator, lhs_retval, *lhs);
        let mut rhs_ctx = codegen_expr(lhs_ctx, allocator, ret_val, *rhs);

        rhs_ctx.get_active_block_mut().map(|block| {
            block.inner.push(format!(
                "\tadd{}\t{}, {}\n",
                ret_val.operator_suffix(),
                lhs_retval,
                ret_val
            ))
        });
        rhs_ctx
    })
}

fn codegen_subtraction(
    ctx: BuildContext<Vec<String>>,
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> BuildContext<Vec<String>> {
    allocator.allocate_then(|allocator, rhs_retval| {
        let lhs_ctx = codegen_expr(ctx, allocator, ret_val, *lhs);
        let mut rhs_ctx = codegen_expr(lhs_ctx, allocator, rhs_retval, *rhs);

        rhs_ctx.get_active_block_mut().map(|block| {
            block.inner.push(format!(
                "\tsub{}\t{}, {}\n",
                ret_val.operator_suffix(),
                rhs_retval,
                ret_val,
            ))
        });
        rhs_ctx
    })
}

fn codegen_multiplication(
    ctx: BuildContext<Vec<String>>,
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> BuildContext<Vec<String>> {
    allocator.allocate_then(|allocator, lhs_retval| {
        let lhs_ctx = codegen_expr(ctx, allocator, lhs_retval, *lhs);
        let mut rhs_ctx = codegen_expr(lhs_ctx, allocator, ret_val, *rhs);

        rhs_ctx.get_active_block_mut().map(|block| {
            block.inner.push(format!(
                "\timul{}\t{}, {}\n",
                ret_val.operator_suffix(),
                lhs_retval,
                ret_val
            ))
        });
        rhs_ctx
    })
}

fn codegen_division(
    ctx: BuildContext<Vec<String>>,
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> BuildContext<Vec<String>> {
    allocator.allocate_then(|allocator, rhs_retval| {
        let lhs_ctx = codegen_expr(ctx, allocator, ret_val, *lhs);
        let mut rhs_ctx = codegen_expr(lhs_ctx, allocator, rhs_retval, *rhs);
        let operand_suffix = ret_val.operator_suffix();

        rhs_ctx.get_active_block_mut().map(|block| {
            block.inner.push(
                vec![
                    format!("\tmov{}\t{},%rax\n", operand_suffix, ret_val),
                    String::from("\tcqo\n"),
                    format!("\tidiv{}\t{}\n", operand_suffix, rhs_retval),
                    format!("\tmov{}\t%rax,{}\n", operand_suffix, ret_val),
                ]
                .join(""),
            )
        });
        rhs_ctx
    })
}

#[derive(Debug, Clone, Copy)]
enum ComparisonOperation {
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    Equal,
    NotEqual,
}

fn codegen_compare_and_set(
    ctx: BuildContext<Vec<String>>,
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    comparison_op: ComparisonOperation,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> BuildContext<Vec<String>> {
    allocator.allocate_then(|allocator, lhs_retval| {
        let lhs_ctx = codegen_expr(ctx, allocator, lhs_retval, *lhs);
        let mut rhs_ctx = codegen_expr(lhs_ctx, allocator, ret_val, *rhs);

        let set_operator = match comparison_op {
            ComparisonOperation::LessThan => "setl",
            ComparisonOperation::LessEqual => "setle",
            ComparisonOperation::GreaterThan => "setg",
            ComparisonOperation::GreaterEqual => "setge",
            ComparisonOperation::Equal => "sete",
            ComparisonOperation::NotEqual => "setne",
        };

        let operand_suffix = ret_val.operator_suffix();

        rhs_ctx.get_active_block_mut().map(|block| {
            block.inner.push(
                vec![
                    format!("\tcmp{}\t{}, {}\n", operand_suffix, ret_val, lhs_retval),
                    format!(
                        "\t{}\t{}\n",
                        set_operator,
                        SizedGeneralPurpose::Byte(ret_val.id())
                    ),
                    format!("\tandq\t$255,{}\n", ret_val),
                ]
                .join(""),
            )
        });
        rhs_ctx
    })
}

fn codegen_compare_and_jump(
    mut ctx: BuildContext<Vec<String>>,
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    _cond_true_id: BlockId,
    cond_false_id: BlockId,
) -> BuildContext<Vec<String>> {
    allocator.allocate_then(|_, zero_val| {
        let operand_suffix = ret_val.operator_suffix();

        ctx.get_active_block_mut().map(|block| {
            block.inner.push(
                vec![
                    format!("\tandq\t$0,{}\n", zero_val),
                    format!("\tcmp{}\t{}, {}\n", operand_suffix, ret_val, zero_val),
                    format!(
                        "\t{}\t{}\n",
                        "sete",
                        SizedGeneralPurpose::Byte(ret_val.id())
                    ),
                    format!("\tandq\t$255,{}\n", ret_val),
                    format!("\t{}\tL{}\n", "jne", cond_false_id),
                ]
                .into_iter()
                .collect(),
            )
        });
        ctx
    })
}

fn codegen_printint(reg: &mut SizedGeneralPurpose) -> Vec<String> {
    vec![format!(
        "\tmov{}\t{}, %rdi\n\tcall\tprintint\n",
        reg.operator_suffix(),
        reg
    )]
}
