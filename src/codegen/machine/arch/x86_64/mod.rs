use crate::codegen::machine::arch::TargetArchitecture;
use crate::codegen::register::Register;
use crate::{
    ast::{
        typing::{ByteSized, Type},
        ExprNode,
    },
    codegen::CodeGenerationErr,
};
use std::sync::atomic::{AtomicUsize, Ordering};

static BLOCK_ID: AtomicUsize = AtomicUsize::new(0);

/// X86_64 represents the x86_64 bit machine target.
pub struct X86_64;

mod register;
use register::{GPRegisterAllocator, SizedGeneralPurpose};

impl TargetArchitecture for X86_64 {}

/// SymbolTable functions as a tracker for symbols that have been previously
/// declared. For the time being, this only tracks global symbols.
#[derive(Default, Debug, Clone)]
pub struct SymbolTable {
    globals: std::collections::HashMap<String, Type>,
}

impl SymbolTable {
    /// Marks a global variable as having been declared.
    pub fn declare_global(&mut self, kind: Type, identifier: &str) {
        self.globals.insert(identifier.to_string(), kind);
    }

    /// Returns a boolean representing if a global variable has already been
    /// declared.
    pub fn has_global(&mut self, identifier: &str) -> bool {
        self.globals.contains_key(identifier)
    }

    /// Returns a boolian representing if a global variable has already been
    /// declared.
    pub fn kind_of(&mut self, identifier: &str) -> Option<&Type> {
        self.globals.get(identifier)
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
    ret\n\n";

use crate::ast;
use crate::codegen;
use crate::codegen::machine;
use crate::codegen::CodeGenerator;

impl CodeGenerator<SymbolTable, ast::typing::TypedFunctionDeclaration> for X86_64 {
    type Error = CodeGenerationErr;

    fn generate(
        &self,
        symboltable: &mut SymbolTable,
        input: ast::typing::TypedFunctionDeclaration,
    ) -> Result<Vec<String>, CodeGenerationErr> {
        let mut allocator = GPRegisterAllocator::default();
        let (id, block) = (input.id, input.block);

        codegen_statements(&mut allocator, symboltable, block)
            .map(|block| {
                vec![
                    codegen_function_preamble(id),
                    block,
                    codegen_function_postamble(),
                ]
            })
            .map(|output| output.into_iter().flatten().collect())
    }
}

impl CodeGenerator<SymbolTable, ast::typing::TypedCompoundStmts> for X86_64 {
    type Error = CodeGenerationErr;

    fn generate(
        &self,
        symboltable: &mut SymbolTable,
        input: ast::typing::TypedCompoundStmts,
    ) -> Result<Vec<String>, CodeGenerationErr> {
        let mut allocator = GPRegisterAllocator::default();
        codegen_statements(&mut allocator, symboltable, input)
    }
}

fn codegen_statements(
    allocator: &mut GPRegisterAllocator,
    symboltable: &mut SymbolTable,
    input: ast::typing::TypedCompoundStmts,
) -> Result<Vec<String>, CodeGenerationErr> {
    let stmts = Vec::<ast::typing::TypedStmtNode>::from(input);

    stmts
        .into_iter()
        .map(|stmt| codegen_statement(allocator, symboltable, stmt).map(|output| output.join("")))
        .collect::<Result<Vec<String>, _>>()
}

fn codegen_statement(
    allocator: &mut GPRegisterAllocator,
    symboltable: &mut SymbolTable,
    input: ast::typing::TypedStmtNode,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    match input {
        ast::typing::TypedStmtNode::Expression(expr) => allocator
            .allocate_then(|allocator, ret_val| Ok(vec![codegen_expr(allocator, ret_val, expr)])),
        ast::typing::TypedStmtNode::Declaration(_, identifier) => {
            symboltable.declare_global(Type::Uint8, &identifier);
            Ok(vec![codegen_global_symbol(Type::Uint8, &identifier)])
        }
        ast::typing::TypedStmtNode::Assignment(identifier, expr) => symboltable
            .has_global(&identifier)
            .then(|| ())
            .map(|_| {
                allocator.allocate_then(|allocator, ret_val| {
                    vec![
                        codegen_expr(allocator, ret_val, expr),
                        codegen_store_global(ret_val, &identifier),
                    ]
                })
            })
            .ok_or(CodeGenerationErr::UndefinedReference(identifier)),
        // with else case
        ast::typing::TypedStmtNode::If(cond, true_case, Some(false_case)) => {
            codegen_if_statement_with_else(allocator, symboltable, cond, true_case, false_case)
                .map(|insts| vec![insts])
        }
        // without else case
        ast::typing::TypedStmtNode::If(cond, true_case, None) => {
            codegen_if_statement_without_else(allocator, symboltable, cond, true_case)
                .map(|insts| vec![insts])
        }

        ast::typing::TypedStmtNode::While(cond, block) => {
            codegen_while_statement(allocator, symboltable, cond, block).map(|insts| vec![insts])
        }
        ast::typing::TypedStmtNode::For(preop, cond, postop, block) => {
            codegen_for_statement(allocator, symboltable, *preop, cond, *postop, block)
                .map(|insts| vec![insts])
        }
    }
    .map(|insts| insts.into_iter().flatten().collect())
}

macro_rules! flattenable_instructions {
    ($($instruction:expr,)*) => {
        vec![
            $(
                $instruction,
            )*
        ]
        .into_iter()
        .flatten()
        .collect()
    };
}

fn codegen_if_statement_with_else(
    allocator: &mut GPRegisterAllocator,
    symboltable: &mut SymbolTable,
    cond: crate::ast::typing::TypedExprNode,
    true_case: crate::ast::typing::TypedCompoundStmts,
    false_case: crate::ast::typing::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_then(|allocator, ret_val| {
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let exit_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let true_case_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let tctx = codegen_statements(allocator, symboltable, true_case)?;
        let else_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_ctx = codegen_statements(allocator, symboltable, false_case)?;

        Ok(flattenable_instructions!(
            cond_ctx,
            codegen_compare_and_jmp(allocator, ret_val, true_case_block_id, else_block_id),
            codegen_label(true_case_block_id),
            tctx,
            codegen_jump(exit_block_id),
            codegen_label(else_block_id),
            block_ctx,
            codegen_label(exit_block_id),
        ))
    })
}

fn codegen_if_statement_without_else(
    allocator: &mut GPRegisterAllocator,
    symboltable: &mut SymbolTable,
    cond: crate::ast::typing::TypedExprNode,
    true_case: crate::ast::typing::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_then(|allocator, ret_val| {
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let exit_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let true_case_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let tctx = codegen_statements(allocator, symboltable, true_case)?;

        Ok(flattenable_instructions!(
            cond_ctx,
            codegen_compare_and_jmp(allocator, ret_val, true_case_block_id, exit_block_id),
            codegen_label(true_case_block_id),
            tctx,
            codegen_label(exit_block_id),
        ))
    })
}

fn codegen_while_statement(
    allocator: &mut GPRegisterAllocator,
    symboltable: &mut SymbolTable,
    cond: crate::ast::typing::TypedExprNode,
    block: crate::ast::typing::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_then(|allocator, ret_val| {
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let loop_cond_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_start_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_end_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_insts = codegen_statements(allocator, symboltable, block)?;

        Ok(flattenable_instructions!(
            codegen_label(loop_cond_block_id),
            cond_ctx,
            codegen_compare_and_jmp(allocator, ret_val, loop_start_block_id, loop_end_block_id),
            codegen_label(loop_start_block_id),
            block_insts,
            codegen_jump(loop_cond_block_id),
            codegen_label(loop_end_block_id),
        ))
    })
}

fn codegen_for_statement(
    allocator: &mut GPRegisterAllocator,
    symboltable: &mut SymbolTable,
    preop: crate::ast::typing::TypedStmtNode,
    cond: crate::ast::typing::TypedExprNode,
    postop: crate::ast::typing::TypedStmtNode,
    block: crate::ast::typing::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_then(|allocator, ret_val| {
        let preop_ctx = codegen_statement(allocator, symboltable, preop)?;
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let postop_ctx = codegen_statement(allocator, symboltable, postop)?;
        let loop_cond_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_start_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_end_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_insts = codegen_statements(allocator, symboltable, block)?;

        Ok(flattenable_instructions!(
            preop_ctx,
            codegen_label(loop_cond_block_id),
            cond_ctx,
            codegen_compare_and_jmp(allocator, ret_val, loop_start_block_id, loop_end_block_id),
            codegen_label(loop_start_block_id),
            block_insts,
            postop_ctx,
            codegen_jump(loop_cond_block_id),
            codegen_label(loop_end_block_id),
        ))
    })
}

/// Returns a vector-wrapped preamble.
pub fn codegen_preamble() -> Vec<String> {
    vec![String::from(machine::arch::x86_64::CG_PREAMBLE)]
}

pub fn codegen_function_preamble(identifier: String) -> Vec<String> {
    vec![format!(
        "\t.text
    .globl  {name}
    .type   {name}, @function
{name}:
    pushq   %rbp
    movq	%rsp, %rbp\n",
        name = identifier
    )]
}

pub fn codegen_function_postamble() -> Vec<String> {
    vec![String::from(
        "\tmovl $0, %eax
    popq     %rbp
    ret\n\n",
    )]
}

fn codegen_global_symbol(kind: Type, identifier: &str) -> Vec<String> {
    const ALIGNMENT: usize = 16;
    let reserve_bytes = kind.size();

    vec![format!(
        "\t.comm\t{},{},{}\n",
        identifier, reserve_bytes, ALIGNMENT
    )]
}

fn codegen_store_global(ret: &mut SizedGeneralPurpose, identifier: &str) -> Vec<String> {
    vec![format!(
        "\tmov{}\t%{}, {}(%rip)\n",
        ret.operator_suffix(),
        ret.id(),
        identifier
    )]
}

fn codegen_load_global(ret: &mut SizedGeneralPurpose, identifier: &str) -> Vec<String> {
    vec![format!(
        "\tmov{}\t{}(%rip), %{}\n",
        ret.operator_suffix(),
        identifier,
        ret.id()
    )]
}

type BlockId = usize;

fn codegen_label(block_id: BlockId) -> Vec<String> {
    vec![format!("L{}:\n", block_id)]
}

fn codegen_jump(block_id: BlockId) -> Vec<String> {
    vec![format!("\tjmp\tL{}\n", block_id)]
}

fn codegen_expr(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    expr: crate::ast::typing::TypedExprNode,
) -> Vec<String> {
    use crate::ast::typing::{Primary, TypedExprNode};

    match expr {
        TypedExprNode::Primary(_, Primary::Uint8(ast::typing::Uint8(uc))) => {
            codegen_constant_u8(ret_val, uc)
        }
        TypedExprNode::Primary(_, Primary::Identifier(_, identifier)) => {
            codegen_load_global(ret_val, &identifier)
        }

        TypedExprNode::Equal(_, lhs, rhs) => {
            codegen_compare_and_set(allocator, ret_val, ComparisonOperation::Equal, lhs, rhs)
        }
        TypedExprNode::NotEqual(_, lhs, rhs) => {
            codegen_compare_and_set(allocator, ret_val, ComparisonOperation::NotEqual, lhs, rhs)
        }
        TypedExprNode::LessThan(_, lhs, rhs) => {
            codegen_compare_and_set(allocator, ret_val, ComparisonOperation::LessThan, lhs, rhs)
        }
        TypedExprNode::GreaterThan(_, lhs, rhs) => codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::GreaterThan,
            lhs,
            rhs,
        ),
        TypedExprNode::LessEqual(_, lhs, rhs) => {
            codegen_compare_and_set(allocator, ret_val, ComparisonOperation::LessEqual, lhs, rhs)
        }
        TypedExprNode::GreaterEqual(_, lhs, rhs) => codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::GreaterEqual,
            lhs,
            rhs,
        ),

        TypedExprNode::Addition(_, lhs, rhs) => codegen_addition(allocator, ret_val, lhs, rhs),
        TypedExprNode::Subtraction(_, lhs, rhs) => {
            codegen_subtraction(allocator, ret_val, lhs, rhs)
        }
        TypedExprNode::Multiplication(_, lhs, rhs) => {
            codegen_multiplication(allocator, ret_val, lhs, rhs)
        }
        TypedExprNode::Division(_, lhs, rhs) => codegen_division(allocator, ret_val, lhs, rhs),
    }
}

fn codegen_constant_u8(ret_val: &mut SizedGeneralPurpose, constant: u8) -> Vec<String> {
    vec![format!(
        "\tmov{}\t${}, {}\n",
        ret_val.operator_suffix(),
        constant,
        ret_val
    )]
}

fn codegen_addition(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    lhs: Box<ast::typing::TypedExprNode>,
    rhs: Box<ast::typing::TypedExprNode>,
) -> Vec<String> {
    allocator.allocate_then(|allocator, lhs_retval| {
        let lhs_ctx = codegen_expr(allocator, lhs_retval, *lhs);
        let rhs_ctx = codegen_expr(allocator, ret_val, *rhs);

        vec![
            lhs_ctx,
            rhs_ctx,
            vec![format!(
                "\tadd{}\t{}, {}\n",
                ret_val.operator_suffix(),
                lhs_retval,
                ret_val
            )],
        ]
        .into_iter()
        .flatten()
        .collect()
    })
}

fn codegen_subtraction(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    lhs: Box<ast::typing::TypedExprNode>,
    rhs: Box<ast::typing::TypedExprNode>,
) -> Vec<String> {
    allocator.allocate_then(|allocator, rhs_retval| {
        let lhs_ctx = codegen_expr(allocator, ret_val, *lhs);
        let rhs_ctx = codegen_expr(allocator, rhs_retval, *rhs);

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![format!(
                "\tsub{}\t{}, {}\n",
                ret_val.operator_suffix(),
                ret_val,
                rhs_retval
            )],
        )
    })
}

fn codegen_multiplication(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    lhs: Box<ast::typing::TypedExprNode>,
    rhs: Box<ast::typing::TypedExprNode>,
) -> Vec<String> {
    allocator.allocate_then(|allocator, lhs_retval| {
        let lhs_ctx = codegen_expr(allocator, lhs_retval, *lhs);
        let rhs_ctx = codegen_expr(allocator, ret_val, *rhs);

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![format!(
                "\timul{}\t{}, {}\n",
                ret_val.operator_suffix(),
                lhs_retval,
                ret_val
            )],
        )
    })
}

fn codegen_division(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    lhs: Box<ast::typing::TypedExprNode>,
    rhs: Box<ast::typing::TypedExprNode>,
) -> Vec<String> {
    allocator.allocate_then(|allocator, rhs_retval| {
        let lhs_ctx = codegen_expr(allocator, ret_val, *lhs);
        let rhs_ctx = codegen_expr(allocator, rhs_retval, *rhs);
        let operand_suffix = ret_val.operator_suffix();

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![
                format!("\tmov{}\t{},%rax\n", operand_suffix, ret_val),
                String::from("\tcqo\n"),
                format!("\tidiv{}\t{}\n", operand_suffix, rhs_retval),
                format!("\tmov{}\t%rax,{}\n", operand_suffix, ret_val),
            ],
        )
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
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    comparison_op: ComparisonOperation,
    lhs: Box<ast::typing::TypedExprNode>,
    rhs: Box<ast::typing::TypedExprNode>,
) -> Vec<String> {
    allocator.allocate_then(|allocator, lhs_retval| {
        let lhs_ctx = codegen_expr(allocator, lhs_retval, *lhs);
        let rhs_ctx = codegen_expr(allocator, ret_val, *rhs);

        let set_operator = match comparison_op {
            ComparisonOperation::LessThan => "setl",
            ComparisonOperation::LessEqual => "setle",
            ComparisonOperation::GreaterThan => "setg",
            ComparisonOperation::GreaterEqual => "setge",
            ComparisonOperation::Equal => "sete",
            ComparisonOperation::NotEqual => "setne",
        };

        let operand_suffix = ret_val.operator_suffix();

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![
                format!("\tcmp{}\t{}, {}\n", operand_suffix, ret_val, lhs_retval),
                format!(
                    "\t{}\t{}\n",
                    set_operator,
                    SizedGeneralPurpose::Byte(ret_val.id())
                ),
                format!("\tandq\t$255,{}\n", ret_val),
            ],
        )
    })
}

fn codegen_compare_and_jmp(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    cond_true_id: BlockId,
    cond_false_id: BlockId,
) -> Vec<String> {
    let operand_suffix = ret_val.operator_suffix();
    allocator.allocate_then(|_, zero_val| {
        vec![
            format!("\tandq\t$0,{}\n", zero_val),
            format!("\tcmp{}\t{}, {}\n", operand_suffix, ret_val, zero_val),
            format!(
                "\t{}\t{}\n",
                "sete",
                SizedGeneralPurpose::Byte(ret_val.id())
            ),
            format!("\tandq\t$255,{}\n", ret_val),
            format!("\t{}\tL{}\n", "je", cond_true_id),
        ]
        .into_iter()
        .chain(codegen_jump(cond_false_id).into_iter())
        .collect()
    })
}

#[allow(dead_code)]
fn codegen_printint(reg: &mut SizedGeneralPurpose) -> Vec<String> {
    vec![format!(
        "\tmov{}\t{}, %rdi\n\tcall\tprintint\n",
        reg.operator_suffix(),
        reg
    )]
}
