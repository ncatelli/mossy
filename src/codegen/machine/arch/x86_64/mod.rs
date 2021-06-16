use crate::codegen::machine::arch::TargetArchitecture;
use crate::codegen::register::Register;
use crate::{ast::ExprNode, codegen::CodeGenerationErr};

type BlockId = usize;

#[derive(Debug, Clone)]
struct Block<T> {
    entry: Option<BlockId>,
    inner: Vec<T>,
    exit_cond_true: Option<BlockId>,
    exit_cond_false: Option<BlockId>,
}

impl<T> Block<T> {
    fn new(
        entry: Option<BlockId>,
        inner: Vec<T>,
        exit_cond_true: Option<BlockId>,
        exit_cond_false: Option<BlockId>,
    ) -> Self {
        Self {
            entry,
            inner,
            exit_cond_true,
            exit_cond_false,
        }
    }
}

impl<T> Default for Block<T> {
    fn default() -> Self {
        Self {
            entry: None,
            inner: Vec::new(),
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

impl<BT> BuildContext<BT> {
    pub fn get_active_block_mut(&mut self) -> Option<&mut Block<BT>> {
        self.blocks.get_mut(self.active_block)
    }

    pub fn get_mut(&mut self, block_id: BlockId) -> Option<&mut Block<BT>> {
        self.blocks.get_mut(block_id)
    }

    pub fn derive_child_from_parent(&mut self, parent: BlockId) -> BlockId {
        let child = <Block<BT>>::new(Some(parent), vec![], None, None);
        self.blocks.push(child);

        self.blocks.len() + 1
    }
}

impl<BT> Default for BuildContext<BT> {
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
    movq	%rsp, %rbp\n";

/// Defines a constant postamble to be appended to any compiled binaries.
pub const CG_POSTAMBLE: &str = "\tmovl	$0, %eax
    popq	%rbp
    ret\n";

use crate::ast;
use crate::codegen;
use crate::codegen::machine;
use crate::codegen::CodeGenerator;

impl CodeGenerator<SymbolTable> for X86_64 {
    fn generate(
        self,
        symboltable: &mut SymbolTable,
        input: ast::StmtNode,
    ) -> Result<Vec<String>, codegen::CodeGenerationErr> {
        let mut allocator = GPRegisterAllocator::default();
        let build_ctx = BuildContext::<Vec<String>>::default();

        let blocks =
            codegen_statement(build_ctx, &mut allocator, symboltable, input).map(|insts| {
                insts
                    .blocks
                    .into_iter()
                    .flat_map(|block| block.inner)
                    .flatten()
                    .collect()
            });

        println!("{:#?}", &blocks);

        blocks
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

/// Returns a vector-wrapped preamble.
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
                block.inner.push(codegen_printint(ret_val));
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
        ast::StmtNode::If(_cond, _true_case, _false_case) => Ok(ctx),
    }
}

fn codegen_global_symbol(
    mut ctx: BuildContext<Vec<String>>,
    identifier: &str,
) -> BuildContext<Vec<String>> {
    ctx.get_active_block_mut().map(|block| {
        block
            .inner
            .push(vec![format!("\t.comm\t{},1,8\n", identifier)])
    });
    ctx
}

fn codegen_store_global(
    mut ctx: BuildContext<Vec<String>>,
    ret: &mut SizedGeneralPurpose,
    identifier: &str,
) -> BuildContext<Vec<String>> {
    ctx.get_active_block_mut().map(|block| {
        block.inner.push(vec![format!(
            "\tmov{}\t%{}, {}(%rip)\n",
            ret.operator_suffix(),
            ret.id(),
            identifier
        )])
    });
    ctx
}

fn codegen_load_global(
    mut ctx: BuildContext<Vec<String>>,
    ret: &mut SizedGeneralPurpose,
    identifier: &str,
) -> BuildContext<Vec<String>> {
    ctx.get_active_block_mut().map(|block| {
        block.inner.push(vec![format!(
            "\tmov{}\t{}(%rip), %{}\n",
            ret.operator_suffix(),
            identifier,
            ret.id()
        )])
    });
    ctx
}

fn codegen_if_statement(
    mut ctx: BuildContext<Vec<String>>,
    allocator: &mut GPRegisterAllocator,
    cond: crate::ast::ExprNode,
    true_case: Vec<String>,
    false_case: Option<Vec<String>>,
) -> BuildContext<Vec<String>> {
    let mut cond_ctx = allocator.allocate_then(|allocator, ret_val| {
        ctx = codegen_expr(ctx, allocator, ret_val, cond);
        ctx.get_active_block_mut().map(|block| {
            block.inner.push(codegen_printint(ret_val));
        });
        ctx
    });

    let cond_id = cond_ctx.active_block;
    let true_block_id = cond_ctx.derive_child_from_parent(cond_id);
    cond_ctx
        .get_mut(true_block_id)
        .map(|block| block.inner.push(true_case));

    // Set exit blocks on parent
    cond_ctx
        .get_mut(cond_id)
        .map(|block| block.exit_cond_true = Some(true_block_id));

    let false_block_id = cond_ctx.derive_child_from_parent(cond_id);
    false_case.map(|fc| {
        cond_ctx
            .get_mut(false_block_id)
            .map(|block| block.inner.push(fc))
    });

    cond_ctx
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

        ExprNode::Equal(lhs, rhs) => codegen_compare(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::Equal,
            lhs,
            rhs,
        ),
        ExprNode::NotEqual(lhs, rhs) => codegen_compare(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::NotEqual,
            lhs,
            rhs,
        ),
        ExprNode::LessThan(lhs, rhs) => codegen_compare(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::LessThan,
            lhs,
            rhs,
        ),
        ExprNode::GreaterThan(lhs, rhs) => codegen_compare(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::GreaterThan,
            lhs,
            rhs,
        ),
        ExprNode::LessEqual(lhs, rhs) => codegen_compare(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::LessEqual,
            lhs,
            rhs,
        ),
        ExprNode::GreaterEqual(lhs, rhs) => codegen_compare(
            ctx,
            allocator,
            ret_val,
            ComparisonOperation::GreaterEqual,
            lhs,
            rhs,
        ),
        ExprNode::Addition(lhs, rhs) => codegen_addition(ctx, allocator, ret_val, lhs, rhs),
        ExprNode::Subtraction(lhs, rhs) => codegen_subtraction(ctx, allocator, ret_val, lhs, rhs),
        ExprNode::Multiplication(lhs, rhs) => {
            codegen_multiplication(ctx, allocator, ret_val, lhs, rhs)
        }
        ExprNode::Division(lhs, rhs) => codegen_division(ctx, allocator, ret_val, lhs, rhs),
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
            block.inner.push(vec![format!(
                "\tadd{}\t{}, {}\n",
                ret_val.operator_suffix(),
                lhs_retval,
                ret_val
            )])
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
            block.inner.push(vec![format!(
                "\tsub{}\t{}, {}\n",
                ret_val.operator_suffix(),
                ret_val,
                rhs_retval
            )])
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
            block.inner.push(vec![format!(
                "\timul{}\t{}, {}\n",
                ret_val.operator_suffix(),
                lhs_retval,
                ret_val
            )])
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
            block.inner.push(vec![
                format!("\tmov{}\t{},%rax\n", operand_suffix, ret_val),
                String::from("\tcqo\n"),
                format!("\tidiv{}\t{}\n", operand_suffix, rhs_retval),
                format!("\tmov{}\t%rax,{}\n", operand_suffix, ret_val),
            ])
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

fn codegen_compare(
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
            block.inner.push(vec![
                format!("\tcmp{}\t{}, {}\n", operand_suffix, ret_val, lhs_retval),
                format!(
                    "\t{}\t{}\n",
                    set_operator,
                    SizedGeneralPurpose::Byte(ret_val.id())
                ),
                format!("\tandq\t$255,{}\n", ret_val),
            ])
        });
        rhs_ctx
    })
}

fn codegen_printint(reg: &mut SizedGeneralPurpose) -> Vec<String> {
    vec![format!(
        "\tmov{}\t{}, %rdi\n\tcall\tprintint\n",
        reg.operator_suffix(),
        reg
    )]
}
