use crate::stage::ast::{self, ByteSized, Type, Typed};
use crate::stage::codegen::machine::arch::TargetArchitecture;
use crate::stage::codegen::{self, CodeGenerationErr};
use crate::stage::CompilationStage;
use core::sync::atomic::{AtomicUsize, Ordering};

static BLOCK_ID: AtomicUsize = AtomicUsize::new(0);

mod allocator;
use allocator::{
    register::{
        BasePointerRegister, GPRegisterAllocator, GeneralPurposeRegister, OperandWidth,
        PointerRegister, ScalarRegister, WidthFormatted,
    },
    SysVAllocator,
};

use crate::stage::slotted_type_check;

/// X86_64 represents the x86_64 bit machine target.
pub struct X86_64;

impl TargetArchitecture for X86_64 {}

impl CompilationStage<ast::TypedProgram, Vec<String>, String> for X86_64 {
    fn apply(&mut self, input: ast::TypedProgram) -> Result<Vec<String>, String> {
        input
            .defs
            .into_iter()
            .map(|global_decl| {
                let res: Result<Vec<String>, CodeGenerationErr> = match global_decl {
                    ast::TypedGlobalDecls::Func(func) => self.apply(func),
                    ast::TypedGlobalDecls::Var(ast::Declaration::Scalar(ty, identifiers)) => {
                        let globals = identifiers
                            .iter()
                            .map(|id| codegen_global_symbol(&ty, id, 1))
                            .flatten()
                            .collect();
                        Ok(globals)
                    }
                    ast::TypedGlobalDecls::Var(ast::Declaration::Array { ty, id, size }) => {
                        Ok(codegen_global_symbol(&ty, &id, size))
                    }
                };

                res
            })
            .collect::<Result<Vec<Vec<String>>, CodeGenerationErr>>()
            .map(|insts| insts.into_iter().flatten().collect())
            .map_err(|e| format!("{:?}", e))
    }
}

// slotted
impl CompilationStage<slotted_type_check::ast::TypedProgram, Vec<String>, String> for X86_64 {
    fn apply(
        &mut self,
        input: slotted_type_check::ast::TypedProgram,
    ) -> Result<Vec<String>, String> {
        input
            .defs
            .into_iter()
            .map(|global_decl| {
                let res: Result<Vec<String>, CodeGenerationErr> = match global_decl {
                    slotted_type_check::ast::TypedGlobalDecls::Func(func) => self.apply(func),
                    slotted_type_check::ast::TypedGlobalDecls::Var(
                        slotted_type_check::ast::Declaration::Scalar(ty, identifiers),
                    ) => {
                        let globals = identifiers
                            .iter()
                            .map(|id| slotted_codegen_global_symbol(&ty, id, 1))
                            .flatten()
                            .collect();
                        Ok(globals)
                    }
                    slotted_type_check::ast::TypedGlobalDecls::Var(
                        slotted_type_check::ast::Declaration::Array { ty, id, size },
                    ) => Ok(slotted_codegen_global_symbol(&ty, &id, size)),
                };

                res
            })
            .collect::<Result<Vec<Vec<String>>, CodeGenerationErr>>()
            .map(|insts| insts.into_iter().flatten().collect())
            .map_err(|e| format!("{:?}", e))
    }
}

impl CompilationStage<ast::TypedFunctionDeclaration, Vec<String>, CodeGenerationErr> for X86_64 {
    fn apply(
        &mut self,
        input: ast::TypedFunctionDeclaration,
    ) -> Result<Vec<String>, CodeGenerationErr> {
        let mut allocator = SysVAllocator::new(GPRegisterAllocator::default());
        let alignment = input.alignment();
        let (id, block) = (input.id, input.block);

        codegen_statements(&mut allocator, block)
            .map(|block| {
                vec![
                    codegen_function_preamble(&id, alignment),
                    block,
                    codegen_function_postamble(&id, alignment),
                ]
            })
            .map(|output| output.into_iter().flatten().collect())
    }
}

// slotted
impl
    CompilationStage<
        slotted_type_check::ast::TypedFunctionDeclaration,
        Vec<String>,
        CodeGenerationErr,
    > for X86_64
{
    fn apply(
        &mut self,
        input: slotted_type_check::ast::TypedFunctionDeclaration,
    ) -> Result<Vec<String>, CodeGenerationErr> {
        let mut allocator = SysVAllocator::new(GPRegisterAllocator::default());
        allocator.allocate_new_local_stack_scope(|allocator| {
            let (id, block) = (input.id, input.block);

            slotted_codegen_statements(allocator, block)
                .map(|block| {
                    let last = allocator
                        .local_stack_offsets
                        .last()
                        .map(|local_declarations| local_declarations.start)
                        .unwrap_or(0);

                    let alignment = allocator.align_stack_pointer(last);
                    vec![
                        codegen_function_preamble(&id, alignment),
                        block,
                        codegen_function_postamble(&id, alignment),
                    ]
                })
                .map(|output| output.into_iter().flatten().collect())
        })
    }
}

// used for testing.
impl CompilationStage<ast::TypedCompoundStmts, Vec<String>, CodeGenerationErr> for X86_64 {
    fn apply(&mut self, input: ast::TypedCompoundStmts) -> Result<Vec<String>, CodeGenerationErr> {
        let mut allocator = SysVAllocator::new(GPRegisterAllocator::default());
        codegen_statements(&mut allocator, input)
    }
}

fn codegen_statements(
    allocator: &mut SysVAllocator,
    input: ast::TypedCompoundStmts,
) -> Result<Vec<String>, CodeGenerationErr> {
    let stmts = Vec::<ast::TypedStmtNode>::from(input);

    stmts
        .into_iter()
        .map(|stmt| codegen_statement(allocator, stmt).map(|output| output.join("")))
        .collect::<Result<Vec<String>, _>>()
}

// slotted
fn slotted_codegen_statements(
    allocator: &mut SysVAllocator,
    input: slotted_type_check::ast::TypedCompoundStmts,
) -> Result<Vec<String>, CodeGenerationErr> {
    let stmts = Vec::<slotted_type_check::ast::TypedStmtNode>::from(input);

    stmts
        .into_iter()
        .map(|stmt| slotted_codegen_statement(allocator, stmt).map(|output| output.join("")))
        .collect::<Result<Vec<String>, _>>()
}

fn codegen_statement(
    allocator: &mut SysVAllocator,
    input: ast::TypedStmtNode,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    match input {
        ast::TypedStmtNode::Expression(expr) => {
            allocator.allocate_gp_register_then(|allocator, ret_val| {
                Ok(vec![codegen_expr(allocator, ret_val, expr)])
            })
        }
        ast::TypedStmtNode::LocalDeclaration(_, _) => Ok(vec![]),
        ast::TypedStmtNode::Return(ty, id, arg) => {
            allocator.allocate_gp_register_then(|allocator, ret_val| {
                let res: Vec<String> = if let Some(expr) = arg {
                    codegen_expr(allocator, ret_val, expr)
                } else {
                    vec![]
                }
                .into_iter()
                .chain(codegen_return(ty, ret_val, &id))
                .collect();

                Ok(vec![res])
            })
        }

        // with else case
        ast::TypedStmtNode::If(cond, true_case, Some(false_case)) => {
            codegen_if_statement_with_else(allocator, cond, true_case, false_case)
                .map(|insts| vec![insts])
        }
        // without else case
        ast::TypedStmtNode::If(cond, true_case, None) => {
            codegen_if_statement_without_else(allocator, cond, true_case).map(|insts| vec![insts])
        }

        ast::TypedStmtNode::While(cond, block) => {
            codegen_while_statement(allocator, cond, block).map(|insts| vec![insts])
        }
        ast::TypedStmtNode::For(preop, cond, postop, block) => {
            codegen_for_statement(allocator, *preop, cond, *postop, block).map(|insts| vec![insts])
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

fn slotted_codegen_statement(
    allocator: &mut SysVAllocator,
    input: slotted_type_check::ast::TypedStmtNode,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    match input {
        slotted_type_check::ast::TypedStmtNode::Expression(expr) => allocator
            .allocate_gp_register_then(|allocator, ret_val| {
                Ok(vec![slotted_codegen_expr(allocator, ret_val, expr)])
            }),
        slotted_type_check::ast::TypedStmtNode::LocalDeclaration(dec, slot_ids) => {
            match dec {
                slotted_type_check::ast::Declaration::Scalar(ty, _) => {
                    for slot in slot_ids {
                        allocator.calculate_and_insert_local_offset(slot, ty.clone());
                    }
                }
                slotted_type_check::ast::Declaration::Array { ty, size, .. } => {
                    let slot = slot_ids.last().ok_or_else(|| {
                        codegen::CodeGenerationErr::UndefinedReference(
                            "no array slot ids for local array declaration".to_string(),
                        )
                    })?;
                    allocator.calculate_and_insert_local_offset_with_cnt(*slot, ty, size);
                }
            };

            Ok(vec![])
        }
        slotted_type_check::ast::TypedStmtNode::Return(ty, id, arg) => allocator
            .allocate_gp_register_then(|allocator, ret_val| {
                let res: Vec<String> = if let Some(expr) = arg {
                    slotted_codegen_expr(allocator, ret_val, expr)
                } else {
                    vec![]
                }
                .into_iter()
                .chain(slotted_codegen_return(ty, ret_val, &id))
                .collect();

                Ok(vec![res])
            }),

        // with else case
        slotted_type_check::ast::TypedStmtNode::If(cond, true_case, Some(false_case)) => {
            slotted_codegen_if_statement_with_else(allocator, cond, true_case, false_case)
                .map(|insts| vec![insts])
        }
        // without else case
        slotted_type_check::ast::TypedStmtNode::If(cond, true_case, None) => {
            slotted_codegen_if_statement_without_else(allocator, cond, true_case)
                .map(|insts| vec![insts])
        }

        slotted_type_check::ast::TypedStmtNode::While(cond, block) => {
            slotted_codegen_while_statement(allocator, cond, block).map(|insts| vec![insts])
        }
        slotted_type_check::ast::TypedStmtNode::For(preop, cond, postop, block) => {
            slotted_codegen_for_statement(allocator, *preop, cond, *postop, block)
                .map(|insts| vec![insts])
        }
    }
    .map(|insts| insts.into_iter().flatten().collect())
}

fn codegen_if_statement_with_else(
    allocator: &mut SysVAllocator,
    cond: ast::TypedExprNode,
    true_case: ast::TypedCompoundStmts,
    false_case: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_gp_register_then(|allocator, ret_val| {
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let exit_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let true_case_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let tctx = codegen_statements(allocator, true_case)?;
        let else_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_ctx = codegen_statements(allocator, false_case)?;

        Ok(flattenable_instructions!(
            cond_ctx,
            codegen_compare_and_jmp(
                allocator,
                ret_val,
                LLabelPrefix(true_case_block_id),
                LLabelPrefix(else_block_id)
            ),
            codegen_label(LLabelPrefix(true_case_block_id)),
            tctx,
            codegen_jump(LLabelPrefix(exit_block_id)),
            codegen_label(LLabelPrefix(else_block_id)),
            block_ctx,
            codegen_label(LLabelPrefix(exit_block_id)),
        ))
    })
}

fn slotted_codegen_if_statement_with_else(
    allocator: &mut SysVAllocator,
    cond: slotted_type_check::ast::TypedExprNode,
    true_case: slotted_type_check::ast::TypedCompoundStmts,
    false_case: slotted_type_check::ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_gp_register_then(|allocator, ret_val| {
        let cond_ctx = slotted_codegen_expr(allocator, ret_val, cond);
        let exit_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let true_case_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let tctx = slotted_codegen_statements(allocator, true_case)?;
        let else_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_ctx = slotted_codegen_statements(allocator, false_case)?;

        Ok(flattenable_instructions!(
            cond_ctx,
            codegen_compare_and_jmp(
                allocator,
                ret_val,
                LLabelPrefix(true_case_block_id),
                LLabelPrefix(else_block_id)
            ),
            codegen_label(LLabelPrefix(true_case_block_id)),
            tctx,
            codegen_jump(LLabelPrefix(exit_block_id)),
            codegen_label(LLabelPrefix(else_block_id)),
            block_ctx,
            codegen_label(LLabelPrefix(exit_block_id)),
        ))
    })
}

fn codegen_if_statement_without_else(
    allocator: &mut SysVAllocator,
    cond: ast::TypedExprNode,
    true_case: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_gp_register_then(|allocator, ret_val| {
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let exit_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let true_case_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let tctx = codegen_statements(allocator, true_case)?;

        Ok(flattenable_instructions!(
            cond_ctx,
            codegen_compare_and_jmp(
                allocator,
                ret_val,
                LLabelPrefix(true_case_block_id),
                LLabelPrefix(exit_block_id)
            ),
            codegen_label(LLabelPrefix(true_case_block_id)),
            tctx,
            codegen_label(LLabelPrefix(exit_block_id)),
        ))
    })
}

fn slotted_codegen_if_statement_without_else(
    allocator: &mut SysVAllocator,
    cond: slotted_type_check::ast::TypedExprNode,
    true_case: slotted_type_check::ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_gp_register_then(|allocator, ret_val| {
        let cond_ctx = slotted_codegen_expr(allocator, ret_val, cond);
        let exit_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let true_case_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let tctx = slotted_codegen_statements(allocator, true_case)?;

        Ok(flattenable_instructions!(
            cond_ctx,
            codegen_compare_and_jmp(
                allocator,
                ret_val,
                LLabelPrefix(true_case_block_id),
                LLabelPrefix(exit_block_id)
            ),
            codegen_label(LLabelPrefix(true_case_block_id)),
            tctx,
            codegen_label(LLabelPrefix(exit_block_id)),
        ))
    })
}

fn codegen_while_statement(
    allocator: &mut SysVAllocator,
    cond: ast::TypedExprNode,
    block: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_gp_register_then(|allocator, ret_val| {
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let loop_cond_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_start_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_end_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_insts = codegen_statements(allocator, block)?;

        Ok(flattenable_instructions!(
            codegen_label(LLabelPrefix(loop_cond_block_id)),
            cond_ctx,
            codegen_compare_and_jmp(
                allocator,
                ret_val,
                LLabelPrefix(loop_start_block_id),
                LLabelPrefix(loop_end_block_id)
            ),
            codegen_label(LLabelPrefix(loop_start_block_id)),
            block_insts,
            codegen_jump(LLabelPrefix(loop_cond_block_id)),
            codegen_label(LLabelPrefix(loop_end_block_id)),
        ))
    })
}

fn slotted_codegen_while_statement(
    allocator: &mut SysVAllocator,
    cond: slotted_type_check::ast::TypedExprNode,
    block: slotted_type_check::ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_gp_register_then(|allocator, ret_val| {
        let cond_ctx = slotted_codegen_expr(allocator, ret_val, cond);
        let loop_cond_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_start_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_end_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_insts = slotted_codegen_statements(allocator, block)?;

        Ok(flattenable_instructions!(
            codegen_label(LLabelPrefix(loop_cond_block_id)),
            cond_ctx,
            codegen_compare_and_jmp(
                allocator,
                ret_val,
                LLabelPrefix(loop_start_block_id),
                LLabelPrefix(loop_end_block_id)
            ),
            codegen_label(LLabelPrefix(loop_start_block_id)),
            block_insts,
            codegen_jump(LLabelPrefix(loop_cond_block_id)),
            codegen_label(LLabelPrefix(loop_end_block_id)),
        ))
    })
}

fn codegen_for_statement(
    allocator: &mut SysVAllocator,
    preop: ast::TypedStmtNode,
    cond: ast::TypedExprNode,
    postop: ast::TypedStmtNode,
    block: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_gp_register_then(|allocator, ret_val| {
        let preop_ctx = codegen_statement(allocator, preop)?;
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let postop_ctx = codegen_statement(allocator, postop)?;
        let loop_cond_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_start_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_end_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_insts = codegen_statements(allocator, block)?;

        Ok(flattenable_instructions!(
            preop_ctx,
            codegen_label(LLabelPrefix(loop_cond_block_id)),
            cond_ctx,
            codegen_compare_and_jmp(
                allocator,
                ret_val,
                LLabelPrefix(loop_start_block_id),
                LLabelPrefix(loop_end_block_id)
            ),
            codegen_label(LLabelPrefix(loop_start_block_id)),
            block_insts,
            postop_ctx,
            codegen_jump(LLabelPrefix(loop_cond_block_id)),
            codegen_label(LLabelPrefix(loop_end_block_id)),
        ))
    })
}

fn slotted_codegen_for_statement(
    allocator: &mut SysVAllocator,
    preop: slotted_type_check::ast::TypedStmtNode,
    cond: slotted_type_check::ast::TypedExprNode,
    postop: slotted_type_check::ast::TypedStmtNode,
    block: slotted_type_check::ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_gp_register_then(|allocator, ret_val| {
        let preop_ctx = slotted_codegen_statement(allocator, preop)?;
        let cond_ctx = slotted_codegen_expr(allocator, ret_val, cond);
        let postop_ctx = slotted_codegen_statement(allocator, postop)?;
        let loop_cond_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_start_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_end_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_insts = slotted_codegen_statements(allocator, block)?;

        Ok(flattenable_instructions!(
            preop_ctx,
            codegen_label(LLabelPrefix(loop_cond_block_id)),
            cond_ctx,
            codegen_compare_and_jmp(
                allocator,
                ret_val,
                LLabelPrefix(loop_start_block_id),
                LLabelPrefix(loop_end_block_id)
            ),
            codegen_label(LLabelPrefix(loop_start_block_id)),
            block_insts,
            postop_ctx,
            codegen_jump(LLabelPrefix(loop_cond_block_id)),
            codegen_label(LLabelPrefix(loop_end_block_id)),
        ))
    })
}

pub fn codegen_function_preamble(identifier: &str, alignment: isize) -> Vec<String> {
    vec![format!(
        "\t.text
    .globl  {name}
    .type   {name}, @function
{name}:
    pushq   %rbp
    movq	%rsp, %rbp
    subq    ${alignment}, %rsp\n",
        name = identifier,
        alignment = alignment
    )]
}

pub fn codegen_function_postamble(identifier: &str, alignment: isize) -> Vec<String> {
    codegen_label(format!("func_{}_ret", identifier))
        .into_iter()
        .chain(
            vec![format!(
                "\taddq\t${}, %rsp
    popq\t%rbp
    ret\n\n",
                alignment
            )]
            .into_iter(),
        )
        .collect()
}

fn slotted_codegen_global_symbol(
    ty: &slotted_type_check::ast::Type,
    identifier: &str,
    count: usize,
) -> Vec<String> {
    use slotted_type_check::ast::ByteSized;
    let reserve_bytes = ty.size() * count;

    vec![format!(
        "\t.data\n\t.globl\t{}\n{}:\n\t.zero\t{}\n\t.text\n",
        identifier, identifier, reserve_bytes
    )]
}

fn codegen_global_symbol(ty: &Type, identifier: &str, count: usize) -> Vec<String> {
    let reserve_bytes = ty.size() * count;

    vec![format!(
        "\t.data\n\t.globl\t{}\n{}:\n\t.zero\t{}\n\t.text\n",
        identifier, identifier, reserve_bytes
    )]
}

fn slotted_codegen_store_global(
    ty: slotted_type_check::ast::Type,
    ret: &GeneralPurposeRegister,
    identifier: &str,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);
    vec![format!(
        "\tmov{}\t%{}, {}(%{})\n",
        operator_suffix(width),
        ret.fmt_with_operand_width(width),
        identifier,
        PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord)
    )]
}

fn codegen_store_global(ty: Type, ret: &GeneralPurposeRegister, identifier: &str) -> Vec<String> {
    let width = operand_width_of_type(ty);
    vec![format!(
        "\tmov{}\t%{}, {}(%{})\n",
        operator_suffix(width),
        ret.fmt_with_operand_width(width),
        identifier,
        PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord)
    )]
}

fn codegen_global_str(identifier: &str, str_literal: &[u8]) -> Vec<String> {
    flattenable_instructions!(
        vec!["\t.section .rodata\n".to_string()],
        codegen_label(identifier),
        str_literal
            .iter()
            .map(|c| format!("\t.byte\t{}\n", c))
            .collect::<Vec<String>>(),
        vec!["\t.byte\t0\n".to_string(), "\t.text\n".to_string()],
    )
}

fn slotted_codegen_store_local(
    ty: slotted_type_check::ast::Type,
    ret: &GeneralPurposeRegister,
    offset: isize,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);
    vec![format!(
        "\tmov{}\t%{}, {}(%{})\n",
        operator_suffix(width),
        ret.fmt_with_operand_width(width),
        offset,
        BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
    )]
}

fn codegen_store_local(ty: Type, ret: &GeneralPurposeRegister, offset: isize) -> Vec<String> {
    let width = operand_width_of_type(ty);
    vec![format!(
        "\tmov{}\t%{}, {}(%{})\n",
        operator_suffix(width),
        ret.fmt_with_operand_width(width),
        offset,
        BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
    )]
}

fn slotted_codegen_load_local(
    ty: slotted_type_check::ast::Type,
    ret: &GeneralPurposeRegister,
    offset: isize,
    scale: usize,
) -> Vec<String> {
    use slotted_type_check::ast::ByteSized;

    let scale_by = ty.size() * scale;
    let width = slotted_operand_width_of_type(ty);

    if scale == 0 {
        vec![format!(
            "\tmov{}\t{}(%{}), %{}\n",
            operator_suffix(width),
            offset,
            BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    } else {
        vec![format!(
            "\tmov{}\t{}+{}(%{}), %{}\n",
            operator_suffix(width),
            offset,
            scale_by,
            BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    }
}

fn codegen_load_local(
    ty: Type,
    ret: &GeneralPurposeRegister,
    offset: isize,
    scale: usize,
) -> Vec<String> {
    let scale_by = ty.size() * scale;
    let width = operand_width_of_type(ty);

    if scale == 0 {
        vec![format!(
            "\tmov{}\t{}(%{}), %{}\n",
            operator_suffix(width),
            offset,
            BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    } else {
        vec![format!(
            "\tmov{}\t{}+{}(%{}), %{}\n",
            operator_suffix(width),
            offset,
            scale_by,
            BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IncDecExpression {
    PreIncrement,
    PreDecrement,
    PostIncrement,
    PostDecrement,
}

fn slotted_codegen_inc_or_dec_expression_from_identifier(
    ty: slotted_type_check::ast::Type,
    ret_val: &GeneralPurposeRegister,
    identifier: &str,
    expr_op: IncDecExpression,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty.clone());

    let op = match expr_op {
        IncDecExpression::PreIncrement | IncDecExpression::PostIncrement => format!(
            "\tinc{}\t{}(%{})\n",
            operator_suffix(width),
            identifier,
            PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ),
        IncDecExpression::PreDecrement | IncDecExpression::PostDecrement => format!(
            "\tdec{}\t{}(%{})\n",
            operator_suffix(width),
            identifier,
            PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ),
    };

    match expr_op {
        IncDecExpression::PreIncrement | IncDecExpression::PreDecrement => {
            flattenable_instructions!(
                vec![op],
                slotted_codegen_load_global(ty, ret_val, identifier, 0),
            )
        }
        IncDecExpression::PostIncrement | IncDecExpression::PostDecrement => {
            flattenable_instructions!(
                slotted_codegen_load_global(ty, ret_val, identifier, 0),
                vec![op],
            )
        }
    }
}

fn codegen_inc_or_dec_expression_from_identifier(
    ty: Type,
    ret_val: &GeneralPurposeRegister,
    identifier: &str,
    expr_op: IncDecExpression,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    let op = match expr_op {
        IncDecExpression::PreIncrement | IncDecExpression::PostIncrement => format!(
            "\tinc{}\t{}(%{})\n",
            operator_suffix(width),
            identifier,
            PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ),
        IncDecExpression::PreDecrement | IncDecExpression::PostDecrement => format!(
            "\tdec{}\t{}(%{})\n",
            operator_suffix(width),
            identifier,
            PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ),
    };

    match expr_op {
        IncDecExpression::PreIncrement | IncDecExpression::PreDecrement => {
            flattenable_instructions!(vec![op], codegen_load_global(ty, ret_val, identifier, 0),)
        }
        IncDecExpression::PostIncrement | IncDecExpression::PostDecrement => {
            flattenable_instructions!(codegen_load_global(ty, ret_val, identifier, 0), vec![op],)
        }
    }
}

fn slotted_codegen_inc_or_dec_expression_from_pointer(
    ty: slotted_type_check::ast::Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    expr_op: IncDecExpression,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty.clone());

    allocator.allocate_gp_register_then(|_, ptr_reg| {
        let op = match expr_op {
            IncDecExpression::PreIncrement | IncDecExpression::PostIncrement => format!(
                "\tinc{}\t(%{})\n",
                operator_suffix(width),
                ptr_reg.fmt_with_operand_width(OperandWidth::QuadWord),
            ),
            IncDecExpression::PreDecrement | IncDecExpression::PostDecrement => format!(
                "\tdec{}\t(%{})\n",
                operator_suffix(width),
                ptr_reg.fmt_with_operand_width(OperandWidth::QuadWord),
            ),
        };

        match expr_op {
            IncDecExpression::PreIncrement | IncDecExpression::PreDecrement => {
                flattenable_instructions!(
                    vec![
                        format!(
                            "\tmov{}\t%{}, %{}\n",
                            operator_suffix(OperandWidth::QuadWord),
                            ret_val.fmt_with_operand_width(OperandWidth::QuadWord),
                            ptr_reg.fmt_with_operand_width(OperandWidth::QuadWord)
                        ),
                        op,
                    ],
                    slotted_codegen_deref(ret_val, ty, 0),
                )
            }
            IncDecExpression::PostIncrement | IncDecExpression::PostDecrement => {
                flattenable_instructions!(
                    vec![format!(
                        "\tmov{}\t%{}, %{}\n",
                        operator_suffix(OperandWidth::QuadWord),
                        ret_val.fmt_with_operand_width(OperandWidth::QuadWord),
                        ptr_reg.fmt_with_operand_width(OperandWidth::QuadWord)
                    )],
                    slotted_codegen_deref(ret_val, ty, 0),
                    vec![op],
                )
            }
        }
    })
}

fn codegen_inc_or_dec_expression_from_pointer(
    ty: Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    expr_op: IncDecExpression,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    allocator.allocate_gp_register_then(|_, ptr_reg| {
        let op = match expr_op {
            IncDecExpression::PreIncrement | IncDecExpression::PostIncrement => format!(
                "\tinc{}\t(%{})\n",
                operator_suffix(width),
                ptr_reg.fmt_with_operand_width(OperandWidth::QuadWord),
            ),
            IncDecExpression::PreDecrement | IncDecExpression::PostDecrement => format!(
                "\tdec{}\t(%{})\n",
                operator_suffix(width),
                ptr_reg.fmt_with_operand_width(OperandWidth::QuadWord),
            ),
        };

        match expr_op {
            IncDecExpression::PreIncrement | IncDecExpression::PreDecrement => {
                flattenable_instructions!(
                    vec![
                        format!(
                            "\tmov{}\t%{}, %{}\n",
                            operator_suffix(OperandWidth::QuadWord),
                            ret_val.fmt_with_operand_width(OperandWidth::QuadWord),
                            ptr_reg.fmt_with_operand_width(OperandWidth::QuadWord)
                        ),
                        op,
                    ],
                    codegen_deref(ret_val, ty, 0),
                )
            }
            IncDecExpression::PostIncrement | IncDecExpression::PostDecrement => {
                flattenable_instructions!(
                    vec![format!(
                        "\tmov{}\t%{}, %{}\n",
                        operator_suffix(OperandWidth::QuadWord),
                        ret_val.fmt_with_operand_width(OperandWidth::QuadWord),
                        ptr_reg.fmt_with_operand_width(OperandWidth::QuadWord)
                    )],
                    codegen_deref(ret_val, ty, 0),
                    vec![op],
                )
            }
        }
    })
}

fn slotted_codegen_load_global(
    ty: slotted_type_check::ast::Type,
    ret: &GeneralPurposeRegister,
    identifier: &str,
    scale: usize,
) -> Vec<String> {
    use slotted_type_check::ast::ByteSized;

    let scale_by = ty.size() * scale;
    let width = slotted_operand_width_of_type(ty);

    if scale == 0 {
        vec![format!(
            "\tmov{}\t{}(%{}), %{}\n",
            operator_suffix(width),
            identifier,
            PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    } else {
        vec![format!(
            "\tmov{}\t{}+{}(%{}), %{}\n",
            operator_suffix(width),
            identifier,
            scale_by,
            PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    }
}

fn codegen_load_global(
    ty: Type,
    ret: &GeneralPurposeRegister,
    identifier: &str,
    scale: usize,
) -> Vec<String> {
    let scale_by = ty.size() * scale;
    let width = operand_width_of_type(ty);

    if scale == 0 {
        vec![format!(
            "\tmov{}\t{}(%{}), %{}\n",
            operator_suffix(width),
            identifier,
            PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    } else {
        vec![format!(
            "\tmov{}\t{}+{}(%{}), %{}\n",
            operator_suffix(width),
            identifier,
            scale_by,
            PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    }
}

/// Defines marker traits for objects that can be used to generate labels.
trait LabelFormattable: core::fmt::Display {}

impl LabelFormattable for &str {}
impl LabelFormattable for String {}

trait PrefixedLabel {
    fn fmt_with_prefix(&self) -> String;
}

struct LLabelPrefix<T: core::fmt::Display>(T);

impl<T> PrefixedLabel for LLabelPrefix<T>
where
    T: core::fmt::Display,
{
    fn fmt_with_prefix(&self) -> String {
        format!("L{}", self.0)
    }
}

impl<T> core::fmt::Display for LLabelPrefix<T>
where
    T: core::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.fmt_with_prefix())
    }
}

impl<T: core::fmt::Display> LabelFormattable for LLabelPrefix<T> {}

fn codegen_label<L>(block_id: L) -> Vec<String>
where
    L: LabelFormattable,
{
    vec![format!("{}:\n", block_id)]
}

fn codegen_jump<L>(block_id: L) -> Vec<String>
where
    L: LabelFormattable,
{
    vec![format!("\tjmp\t{}\n", block_id)]
}

fn slotted_codegen_expr(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    expr: slotted_type_check::ast::TypedExprNode,
) -> Vec<String> {
    use crate::stage::slotted_type_check::ast::{
        self, IntegerWidth, Primary, Signed, TypedExprNode,
    };

    match expr {
        TypedExprNode::Primary(_, Primary::Integer { sign, width, value }) => match (sign, width) {
            (_, IntegerWidth::One) => {
                let boolean_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 8-bit integer");
                codegen_constant_u8(ret_val, boolean_literal)
            }

            (Signed::Signed, IntegerWidth::Eight) => {
                let signed_literal = u64::from_le_bytes(value);
                if signed_literal.leading_zeros() >= 56 {
                    codegen_constant_i8(ret_val, signed_literal as i8)
                } else {
                    panic!("value exceeds signed 8-bit integer")
                }
            }
            (Signed::Signed, IntegerWidth::Sixteen) => {
                let signed_literal = u64::from_le_bytes(value);
                if signed_literal.leading_zeros() >= 48 {
                    codegen_constant_i16(ret_val, signed_literal as i16)
                } else {
                    panic!("value exceeds signed 16-bit integer")
                }
            }
            (Signed::Signed, IntegerWidth::ThirtyTwo) => {
                let signed_literal = u64::from_le_bytes(value);
                if signed_literal.leading_zeros() >= 32 {
                    codegen_constant_i32(ret_val, signed_literal as i32)
                } else {
                    panic!("value exceeds signed 32-bit integer")
                }
            }
            (Signed::Signed, IntegerWidth::SixtyFour) => {
                codegen_constant_i64(ret_val, i64::from_le_bytes(value))
            }
            (Signed::Unsigned, IntegerWidth::Eight) => {
                let unsigned_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 8-bit integer");
                codegen_constant_u8(ret_val, unsigned_literal)
            }
            (Signed::Unsigned, IntegerWidth::Sixteen) => {
                let unsigned_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 32-bit integer");
                codegen_constant_u16(ret_val, unsigned_literal)
            }
            (Signed::Unsigned, IntegerWidth::ThirtyTwo) => {
                let unsigned_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 32-bit integer");
                codegen_constant_u32(ret_val, unsigned_literal)
            }
            (Signed::Unsigned, IntegerWidth::SixtyFour) => {
                codegen_constant_u64(ret_val, u64::from_le_bytes(value))
            }
        },

        TypedExprNode::Primary(ty, Primary::Identifier(_, ast::IdentifierLocality::Global(id))) => {
            slotted_codegen_load_global(ty, ret_val, &id, 0)
        }
        TypedExprNode::Primary(
            ty,
            Primary::Identifier(_, ast::IdentifierLocality::Local(slot)),
        ) => allocator
            .get_slot_offset(slot)
            .map(|offset_start| slotted_codegen_load_local(ty, ret_val, offset_start, 0))
            .expect("local stack slot is undeclared"),
        TypedExprNode::Primary(_, Primary::Str(lit)) => {
            let identifier = format!("V{}", BLOCK_ID.fetch_add(1, Ordering::SeqCst));

            flattenable_instructions!(
                codegen_global_str(&identifier, &lit),
                codegen_reference_from_identifier(ret_val, &identifier),
            )
        }

        TypedExprNode::FunctionCall(ty, func_name, optional_arg) => {
            slotted_codegen_call(allocator, ty, ret_val, &func_name, optional_arg)
        }

        ast::TypedExprNode::IdentifierAssignment(
            ty,
            ast::IdentifierLocality::Global(identifier),
            expr,
        ) => {
            flattenable_instructions!(
                slotted_codegen_expr(allocator, ret_val, *expr),
                slotted_codegen_store_global(ty, ret_val, &identifier),
            )
        }
        ast::TypedExprNode::IdentifierAssignment(
            ty,
            ast::IdentifierLocality::Local(slot),
            expr,
        ) => {
            flattenable_instructions!(
                slotted_codegen_expr(allocator, ret_val, *expr),
                allocator
                    .get_slot_offset(slot)
                    .map(|offset_start| { slotted_codegen_store_local(ty, ret_val, offset_start) })
                    .expect("local stack slot is undeclared"),
            )
        }
        TypedExprNode::DerefAssignment(ty, lhs, rhs) => {
            allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
                flattenable_instructions!(
                    slotted_codegen_expr(allocator, rhs_ret_val, *rhs),
                    slotted_codegen_expr(allocator, ret_val, *lhs),
                    slotted_codegen_store_deref(ty, ret_val, rhs_ret_val),
                )
            })
        }

        TypedExprNode::LogOr(_, lhs, rhs) => {
            let ty = generate_type_specifier!(u64);
            slotted_codegen_or(ast::Type::from(ty), allocator, ret_val, *lhs, *rhs)
        }
        TypedExprNode::LogAnd(_, lhs, rhs) => {
            let ty = generate_type_specifier!(u64);
            slotted_codegen_and(ast::Type::from(ty), allocator, ret_val, *lhs, *rhs)
        }

        TypedExprNode::BitOr(ty, lhs, rhs) => {
            slotted_codegen_or(ty, allocator, ret_val, *lhs, *rhs)
        }
        TypedExprNode::BitXor(ty, lhs, rhs) => {
            slotted_codegen_xor(ty, allocator, ret_val, *lhs, *rhs)
        }
        TypedExprNode::BitAnd(ty, lhs, rhs) => {
            slotted_codegen_and(ty, allocator, ret_val, *lhs, *rhs)
        }

        TypedExprNode::Equal(ty, lhs, rhs) => slotted_codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::Equal,
            ty,
            lhs,
            rhs,
        ),
        TypedExprNode::NotEqual(ty, lhs, rhs) => slotted_codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::NotEqual,
            ty,
            lhs,
            rhs,
        ),
        TypedExprNode::LessThan(ty, lhs, rhs) => slotted_codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::LessThan,
            ty,
            lhs,
            rhs,
        ),
        TypedExprNode::GreaterThan(ty, lhs, rhs) => slotted_codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::GreaterThan,
            ty,
            lhs,
            rhs,
        ),
        TypedExprNode::LessEqual(ty, lhs, rhs) => slotted_codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::LessEqual,
            ty,
            lhs,
            rhs,
        ),
        TypedExprNode::GreaterEqual(ty, lhs, rhs) => slotted_codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::GreaterEqual,
            ty,
            lhs,
            rhs,
        ),

        TypedExprNode::BitShiftLeft(ty, lhs, rhs) => {
            slotted_codegen_shift_left(ty, allocator, ret_val, *lhs, *rhs)
        }
        TypedExprNode::BitShiftRight(ty, lhs, rhs) => {
            slotted_codegen_shift_right(ty, allocator, ret_val, *lhs, *rhs)
        }

        TypedExprNode::Addition(ast::Type::Pointer(ty), lhs, rhs) => {
            slotted_codegen_addition(allocator, ret_val, ty.pointer_to(), lhs, rhs)
        }
        TypedExprNode::Addition(ty, lhs, rhs) => {
            slotted_codegen_addition(allocator, ret_val, ty, lhs, rhs)
        }
        TypedExprNode::Subtraction(ty, lhs, rhs) => {
            slotted_codegen_subtraction(allocator, ret_val, ty, lhs, rhs)
        }
        TypedExprNode::Multiplication(ty, lhs, rhs) => {
            slotted_codegen_multiplication(allocator, ret_val, ty, lhs, rhs)
        }
        TypedExprNode::Division(ty, lhs, rhs) => slotted_codegen_division(
            allocator,
            ret_val,
            ty,
            lhs,
            rhs,
            Signed::Unsigned,
            DivisionVariant::Division,
        ),
        TypedExprNode::Modulo(ty, lhs, rhs) => slotted_codegen_division(
            allocator,
            ret_val,
            ty,
            lhs,
            rhs,
            Signed::Unsigned,
            DivisionVariant::Modulo,
        ),

        TypedExprNode::LogicalNot(_, expr) => slotted_codegen_not(allocator, ret_val, *expr),
        TypedExprNode::Negate(_, expr) => slotted_codegen_negate(allocator, ret_val, *expr),
        TypedExprNode::Invert(_, expr) => slotted_codegen_invert(allocator, ret_val, *expr),

        TypedExprNode::PreIncrement(_, expr) => match *expr {
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Global(identifier)),
            ) => slotted_codegen_inc_or_dec_expression_from_identifier(
                ty,
                ret_val,
                &identifier,
                IncDecExpression::PreIncrement,
            ),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    slotted_codegen_expr(allocator, ret_val, *expr),
                    slotted_codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret_val,
                        IncDecExpression::PreIncrement,
                    ),
                )
            }
            _ => unreachable!(),
        },
        TypedExprNode::PreDecrement(_, expr) => match *expr {
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Global(identifier)),
            ) => slotted_codegen_inc_or_dec_expression_from_identifier(
                ty,
                ret_val,
                &identifier,
                IncDecExpression::PreDecrement,
            ),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    slotted_codegen_expr(allocator, ret_val, *expr),
                    slotted_codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret_val,
                        IncDecExpression::PreDecrement,
                    ),
                )
            }
            _ => unreachable!(),
        },
        TypedExprNode::PostIncrement(_, expr) => match *expr {
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Global(identifier)),
            ) => slotted_codegen_inc_or_dec_expression_from_identifier(
                ty,
                ret_val,
                &identifier,
                IncDecExpression::PostIncrement,
            ),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    slotted_codegen_expr(allocator, ret_val, *expr),
                    slotted_codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret_val,
                        IncDecExpression::PostIncrement,
                    ),
                )
            }
            _ => unreachable!(),
        },
        TypedExprNode::PostDecrement(_, expr) => match *expr {
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Global(identifier)),
            ) => slotted_codegen_inc_or_dec_expression_from_identifier(
                ty,
                ret_val,
                &identifier,
                IncDecExpression::PostDecrement,
            ),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    slotted_codegen_expr(allocator, ret_val, *expr),
                    slotted_codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret_val,
                        IncDecExpression::PostDecrement,
                    ),
                )
            }
            _ => unreachable!(),
        },

        TypedExprNode::Ref(_, ast::IdentifierLocality::Global(identifier)) => {
            codegen_reference_from_identifier(ret_val, &identifier)
        }
        TypedExprNode::Ref(_, ast::IdentifierLocality::Local(slot)) => allocator
            .get_slot_offset(slot)
            .map(|offset_start| codegen_reference_from_stack_offset(ret_val, offset_start))
            .expect("local stack slot is undeclared"),
        TypedExprNode::Deref(ty, expr) => {
            flattenable_instructions!(
                slotted_codegen_expr(allocator, ret_val, *expr),
                slotted_codegen_deref(ret_val, ty, 0),
            )
        }
        TypedExprNode::ScaleBy(ty, lhs) => {
            use crate::stage::slotted_type_check::ast::ByteSized;

            let scale_by_size = ty.size();
            slotted_codegen_scaleby(allocator, ret_val, scale_by_size, lhs)
        }
        TypedExprNode::Grouping(_, expr) => slotted_codegen_expr(allocator, ret_val, *expr),
    }
}

fn codegen_expr(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    expr: ast::TypedExprNode,
) -> Vec<String> {
    use crate::stage::ast::{IntegerWidth, Primary, Signed, TypedExprNode};

    match expr {
        TypedExprNode::Primary(_, Primary::Integer { sign, width, value }) => match (sign, width) {
            (_, IntegerWidth::One) => {
                let boolean_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 8-bit integer");
                codegen_constant_u8(ret_val, boolean_literal)
            }

            (Signed::Signed, IntegerWidth::Eight) => {
                let signed_literal = u64::from_le_bytes(value);
                if signed_literal.leading_zeros() >= 56 {
                    codegen_constant_i8(ret_val, signed_literal as i8)
                } else {
                    panic!("value exceeds signed 8-bit integer")
                }
            }
            (Signed::Signed, IntegerWidth::Sixteen) => {
                let signed_literal = u64::from_le_bytes(value);
                if signed_literal.leading_zeros() >= 48 {
                    codegen_constant_i16(ret_val, signed_literal as i16)
                } else {
                    panic!("value exceeds signed 16-bit integer")
                }
            }
            (Signed::Signed, IntegerWidth::ThirtyTwo) => {
                let signed_literal = u64::from_le_bytes(value);
                if signed_literal.leading_zeros() >= 32 {
                    codegen_constant_i32(ret_val, signed_literal as i32)
                } else {
                    panic!("value exceeds signed 32-bit integer")
                }
            }
            (Signed::Signed, IntegerWidth::SixtyFour) => {
                codegen_constant_i64(ret_val, i64::from_le_bytes(value))
            }
            (Signed::Unsigned, IntegerWidth::Eight) => {
                let unsigned_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 8-bit integer");
                codegen_constant_u8(ret_val, unsigned_literal)
            }
            (Signed::Unsigned, IntegerWidth::Sixteen) => {
                let unsigned_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 32-bit integer");
                codegen_constant_u16(ret_val, unsigned_literal)
            }
            (Signed::Unsigned, IntegerWidth::ThirtyTwo) => {
                let unsigned_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 32-bit integer");
                codegen_constant_u32(ret_val, unsigned_literal)
            }
            (Signed::Unsigned, IntegerWidth::SixtyFour) => {
                codegen_constant_u64(ret_val, u64::from_le_bytes(value))
            }
        },

        TypedExprNode::Primary(ty, Primary::Identifier(_, ast::IdentifierLocality::Global(id))) => {
            codegen_load_global(ty, ret_val, &id, 0)
        }
        TypedExprNode::Primary(
            ty,
            Primary::Identifier(_, ast::IdentifierLocality::Local(offset)),
        ) => codegen_load_local(ty, ret_val, offset, 0),
        TypedExprNode::Primary(_, Primary::Str(lit)) => {
            let identifier = format!("V{}", BLOCK_ID.fetch_add(1, Ordering::SeqCst));

            flattenable_instructions!(
                codegen_global_str(&identifier, &lit),
                codegen_reference_from_identifier(ret_val, &identifier),
            )
        }

        TypedExprNode::FunctionCall(ty, func_name, optional_arg) => {
            codegen_call(allocator, ty, ret_val, &func_name, optional_arg)
        }

        ast::TypedExprNode::IdentifierAssignment(
            ty,
            ast::IdentifierLocality::Global(identifier),
            expr,
        ) => {
            flattenable_instructions!(
                codegen_expr(allocator, ret_val, *expr),
                codegen_store_global(ty, ret_val, &identifier),
            )
        }
        ast::TypedExprNode::IdentifierAssignment(
            ty,
            ast::IdentifierLocality::Local(offset),
            expr,
        ) => {
            flattenable_instructions!(
                codegen_expr(allocator, ret_val, *expr),
                codegen_store_local(ty, ret_val, offset),
            )
        }
        TypedExprNode::DerefAssignment(ty, lhs, rhs) => {
            allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
                flattenable_instructions!(
                    codegen_expr(allocator, rhs_ret_val, *rhs),
                    codegen_expr(allocator, ret_val, *lhs),
                    codegen_store_deref(ty, ret_val, rhs_ret_val),
                )
            })
        }

        TypedExprNode::LogOr(_, lhs, rhs) => {
            let ty = generate_type_specifier!(u64);
            codegen_or(ty, allocator, ret_val, *lhs, *rhs)
        }
        TypedExprNode::LogAnd(_, lhs, rhs) => {
            let ty = generate_type_specifier!(u64);
            codegen_and(ty, allocator, ret_val, *lhs, *rhs)
        }

        TypedExprNode::BitOr(ty, lhs, rhs) => codegen_or(ty, allocator, ret_val, *lhs, *rhs),
        TypedExprNode::BitXor(ty, lhs, rhs) => codegen_xor(ty, allocator, ret_val, *lhs, *rhs),
        TypedExprNode::BitAnd(ty, lhs, rhs) => codegen_and(ty, allocator, ret_val, *lhs, *rhs),

        TypedExprNode::Equal(ty, lhs, rhs) => {
            codegen_compare_and_set(allocator, ret_val, ComparisonOperation::Equal, ty, lhs, rhs)
        }
        TypedExprNode::NotEqual(ty, lhs, rhs) => codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::NotEqual,
            ty,
            lhs,
            rhs,
        ),
        TypedExprNode::LessThan(ty, lhs, rhs) => codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::LessThan,
            ty,
            lhs,
            rhs,
        ),
        TypedExprNode::GreaterThan(ty, lhs, rhs) => codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::GreaterThan,
            ty,
            lhs,
            rhs,
        ),
        TypedExprNode::LessEqual(ty, lhs, rhs) => codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::LessEqual,
            ty,
            lhs,
            rhs,
        ),
        TypedExprNode::GreaterEqual(ty, lhs, rhs) => codegen_compare_and_set(
            allocator,
            ret_val,
            ComparisonOperation::GreaterEqual,
            ty,
            lhs,
            rhs,
        ),

        TypedExprNode::BitShiftLeft(ty, lhs, rhs) => {
            codegen_shift_left(ty, allocator, ret_val, *lhs, *rhs)
        }
        TypedExprNode::BitShiftRight(ty, lhs, rhs) => {
            codegen_shift_right(ty, allocator, ret_val, *lhs, *rhs)
        }

        TypedExprNode::Addition(Type::Pointer(ty), lhs, rhs) => {
            codegen_addition(allocator, ret_val, ty.pointer_to(), lhs, rhs)
        }
        TypedExprNode::Addition(ty, lhs, rhs) => codegen_addition(allocator, ret_val, ty, lhs, rhs),
        TypedExprNode::Subtraction(ty, lhs, rhs) => {
            codegen_subtraction(allocator, ret_val, ty, lhs, rhs)
        }
        TypedExprNode::Multiplication(ty, lhs, rhs) => {
            codegen_multiplication(allocator, ret_val, ty, lhs, rhs)
        }
        TypedExprNode::Division(ty, lhs, rhs) => codegen_division(
            allocator,
            ret_val,
            ty,
            lhs,
            rhs,
            Signed::Unsigned,
            DivisionVariant::Division,
        ),
        TypedExprNode::Modulo(ty, lhs, rhs) => codegen_division(
            allocator,
            ret_val,
            ty,
            lhs,
            rhs,
            Signed::Unsigned,
            DivisionVariant::Modulo,
        ),

        TypedExprNode::LogicalNot(_, expr) => codegen_not(allocator, ret_val, *expr),
        TypedExprNode::Negate(_, expr) => codegen_negate(allocator, ret_val, *expr),
        TypedExprNode::Invert(_, expr) => codegen_invert(allocator, ret_val, *expr),

        TypedExprNode::PreIncrement(_, expr) => match *expr {
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Global(identifier)),
            ) => codegen_inc_or_dec_expression_from_identifier(
                ty,
                ret_val,
                &identifier,
                IncDecExpression::PreIncrement,
            ),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    codegen_expr(allocator, ret_val, *expr),
                    codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret_val,
                        IncDecExpression::PreIncrement,
                    ),
                )
            }
            _ => unreachable!(),
        },
        TypedExprNode::PreDecrement(_, expr) => match *expr {
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Global(identifier)),
            ) => codegen_inc_or_dec_expression_from_identifier(
                ty,
                ret_val,
                &identifier,
                IncDecExpression::PreDecrement,
            ),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    codegen_expr(allocator, ret_val, *expr),
                    codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret_val,
                        IncDecExpression::PreDecrement,
                    ),
                )
            }
            _ => unreachable!(),
        },
        TypedExprNode::PostIncrement(_, expr) => match *expr {
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Global(identifier)),
            ) => codegen_inc_or_dec_expression_from_identifier(
                ty,
                ret_val,
                &identifier,
                IncDecExpression::PostIncrement,
            ),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    codegen_expr(allocator, ret_val, *expr),
                    codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret_val,
                        IncDecExpression::PostIncrement,
                    ),
                )
            }
            _ => unreachable!(),
        },
        TypedExprNode::PostDecrement(_, expr) => match *expr {
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Global(identifier)),
            ) => codegen_inc_or_dec_expression_from_identifier(
                ty,
                ret_val,
                &identifier,
                IncDecExpression::PostDecrement,
            ),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    codegen_expr(allocator, ret_val, *expr),
                    codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret_val,
                        IncDecExpression::PostDecrement,
                    ),
                )
            }
            _ => unreachable!(),
        },

        TypedExprNode::Ref(_, ast::IdentifierLocality::Global(identifier)) => {
            codegen_reference_from_identifier(ret_val, &identifier)
        }
        TypedExprNode::Ref(_, ast::IdentifierLocality::Local(offset)) => {
            codegen_reference_from_stack_offset(ret_val, offset)
        }
        TypedExprNode::Deref(ty, expr) => {
            flattenable_instructions!(
                codegen_expr(allocator, ret_val, *expr),
                codegen_deref(ret_val, ty, 0),
            )
        }
        TypedExprNode::ScaleBy(ty, lhs) => {
            let scale_by_size = ty.size();
            codegen_scaleby(allocator, ret_val, scale_by_size, lhs)
        }
        TypedExprNode::Grouping(_, expr) => codegen_expr(allocator, ret_val, *expr),
    }
}

fn codegen_constant_i8(ret_val: &GeneralPurposeRegister, constant: i8) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;
    vec![format!(
        "\tmov{}\t${}, %{}\n",
        operator_suffix(WIDTH),
        constant,
        ret_val.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_u8(ret_val: &GeneralPurposeRegister, constant: u8) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;
    vec![format!(
        "\tmov{}\t${}, %{}\n",
        operator_suffix(WIDTH),
        constant,
        ret_val.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_i16(ret_val: &GeneralPurposeRegister, constant: i16) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, %{}\n",
        operator_suffix(WIDTH),
        constant,
        ret_val.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_u16(ret_val: &GeneralPurposeRegister, constant: u16) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, %{}\n",
        operator_suffix(WIDTH),
        constant,
        ret_val.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_i32(ret_val: &GeneralPurposeRegister, constant: i32) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, %{}\n",
        operator_suffix(WIDTH),
        constant,
        ret_val.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_u32(ret_val: &GeneralPurposeRegister, constant: u32) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, %{}\n",
        operator_suffix(WIDTH),
        constant,
        ret_val.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_i64(ret_val: &GeneralPurposeRegister, constant: i64) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, %{}\n",
        operator_suffix(WIDTH),
        constant,
        ret_val.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_u64(ret_val: &GeneralPurposeRegister, constant: u64) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, %{}\n",
        operator_suffix(WIDTH),
        constant,
        ret_val.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_reference_from_identifier(
    ret: &GeneralPurposeRegister,
    identifier: &str,
) -> Vec<String> {
    vec![format!(
        "\tleaq\t{}(%{}), %{}\n",
        identifier,
        PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ret.fmt_with_operand_width(OperandWidth::QuadWord)
    )]
}

fn codegen_reference_from_stack_offset(ret: &GeneralPurposeRegister, offset: isize) -> Vec<String> {
    vec![format!(
        "\tleaq\t{}(%{}), %{}\n",
        offset,
        BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ret.fmt_with_operand_width(OperandWidth::QuadWord)
    )]
}

fn slotted_codegen_store_deref(
    ty: slotted_type_check::ast::Type,
    dest: &GeneralPurposeRegister,
    src: &GeneralPurposeRegister,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);

    vec![format!(
        "\tmov{}\t%{}, (%{})\n",
        operator_suffix(width),
        src.fmt_with_operand_width(width),
        dest.fmt_with_operand_width(OperandWidth::QuadWord)
    )]
}

fn codegen_store_deref(
    ty: Type,
    dest: &GeneralPurposeRegister,
    src: &GeneralPurposeRegister,
) -> Vec<String> {
    let width = operand_width_of_type(ty);

    vec![format!(
        "\tmov{}\t%{}, (%{})\n",
        operator_suffix(width),
        src.fmt_with_operand_width(width),
        dest.fmt_with_operand_width(OperandWidth::QuadWord)
    )]
}

fn slotted_codegen_deref(
    ret: &GeneralPurposeRegister,
    ty: slotted_type_check::ast::Type,
    scale: usize,
) -> Vec<String> {
    use slotted_type_check::ast::ByteSized;
    let scale_by = ty.size() * scale;
    let width = slotted_operand_width_of_type(ty);

    if scale == 0 {
        vec![format!(
            "\tmov{}\t(%{}), %{}\n",
            operator_suffix(width),
            ret.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    } else {
        vec![format!(
            "\tmov{}\t{}(%{}), %{}\n",
            operator_suffix(width),
            scale_by,
            ret.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    }
}

fn codegen_deref(ret: &GeneralPurposeRegister, ty: ast::Type, scale: usize) -> Vec<String> {
    let scale_by = ty.size() * scale;
    let width = operand_width_of_type(ty);

    if scale == 0 {
        vec![format!(
            "\tmov{}\t(%{}), %{}\n",
            operator_suffix(width),
            ret.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    } else {
        vec![format!(
            "\tmov{}\t{}(%{}), %{}\n",
            operator_suffix(width),
            scale_by,
            ret.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    }
}

fn slotted_codegen_scaleby(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    size_of: usize,
    expr: Box<slotted_type_check::ast::TypedExprNode>,
) -> Vec<String> {
    use slotted_type_check::ast::{self, Typed};

    if let ast::Type::Integer(sign, _) = expr.r#type() {
        let scale_by_expr = ast::TypedExprNode::Primary(
            ast::Type::Integer(sign, ast::IntegerWidth::SixtyFour),
            ast::Primary::Integer {
                sign,
                width: ast::IntegerWidth::SixtyFour,
                value: crate::util::pad_to_64bit_array((size_of as u64).to_le_bytes()),
            },
        );

        slotted_codegen_multiplication(
            allocator,
            ret_val,
            ast::Type::Integer(sign, ast::IntegerWidth::SixtyFour),
            Box::new(scale_by_expr),
            expr,
        )
    } else {
        panic!("invalid scale_by types")
    }
}

fn codegen_scaleby(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    size_of: usize,
    expr: Box<ast::TypedExprNode>,
) -> Vec<String> {
    if let ast::Type::Integer(sign, _) = expr.r#type() {
        let scale_by_expr = ast::TypedExprNode::Primary(
            ast::Type::Integer(sign, ast::IntegerWidth::SixtyFour),
            ast::Primary::Integer {
                sign,
                width: ast::IntegerWidth::SixtyFour,
                value: crate::util::pad_to_64bit_array((size_of as u64).to_le_bytes()),
            },
        );

        codegen_multiplication(
            allocator,
            ret_val,
            ast::Type::Integer(sign, ast::IntegerWidth::SixtyFour),
            Box::new(scale_by_expr),
            expr,
        )
    } else {
        panic!("invalid scale_by types")
    }
}

fn slotted_codegen_addition(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    ty: slotted_type_check::ast::Type,
    lhs: Box<slotted_type_check::ast::TypedExprNode>,
    rhs: Box<slotted_type_check::ast::TypedExprNode>,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, lhs_retval| {
        let lhs_ctx = slotted_codegen_expr(allocator, lhs_retval, *lhs);
        let rhs_ctx = slotted_codegen_expr(allocator, ret_val, *rhs);

        vec![
            lhs_ctx,
            rhs_ctx,
            vec![format!(
                "\tadd{}\t%{}, %{}\n",
                operator_suffix(width),
                lhs_retval.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        ]
        .into_iter()
        .flatten()
        .collect()
    })
}

fn codegen_addition(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    ty: ast::Type,
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
) -> Vec<String> {
    let width = operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, lhs_retval| {
        let lhs_ctx = codegen_expr(allocator, lhs_retval, *lhs);
        let rhs_ctx = codegen_expr(allocator, ret_val, *rhs);

        vec![
            lhs_ctx,
            rhs_ctx,
            vec![format!(
                "\tadd{}\t%{}, %{}\n",
                operator_suffix(width),
                lhs_retval.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        ]
        .into_iter()
        .flatten()
        .collect()
    })
}

fn slotted_codegen_subtraction(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    ty: slotted_type_check::ast::Type,
    lhs: Box<slotted_type_check::ast::TypedExprNode>,
    rhs: Box<slotted_type_check::ast::TypedExprNode>,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let lhs_ctx = slotted_codegen_expr(allocator, ret_val, *lhs);
        let rhs_ctx = slotted_codegen_expr(allocator, rhs_ret_val, *rhs);

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![format!(
                "\tsub{}\t%{}, %{}\n",
                operator_suffix(width),
                rhs_ret_val.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        )
    })
}

fn codegen_subtraction(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    ty: ast::Type,
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
) -> Vec<String> {
    let width = operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let lhs_ctx = codegen_expr(allocator, ret_val, *lhs);
        let rhs_ctx = codegen_expr(allocator, rhs_ret_val, *rhs);

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![format!(
                "\tsub{}\t%{}, %{}\n",
                operator_suffix(width),
                rhs_ret_val.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        )
    })
}

fn slotted_codegen_multiplication(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    ty: slotted_type_check::ast::Type,
    lhs: Box<slotted_type_check::ast::TypedExprNode>,
    rhs: Box<slotted_type_check::ast::TypedExprNode>,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, lhs_retval| {
        let lhs_ctx = slotted_codegen_expr(allocator, lhs_retval, *lhs);
        let rhs_ctx = slotted_codegen_expr(allocator, ret_val, *rhs);

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![format!(
                "\timul{}\t%{}, %{}\n",
                operator_suffix(width),
                lhs_retval.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        )
    })
}

fn codegen_multiplication(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    ty: ast::Type,
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
) -> Vec<String> {
    let width = operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, lhs_retval| {
        let lhs_ctx = codegen_expr(allocator, lhs_retval, *lhs);
        let rhs_ctx = codegen_expr(allocator, ret_val, *rhs);

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![format!(
                "\timul{}\t%{}, %{}\n",
                operator_suffix(width),
                lhs_retval.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        )
    })
}

#[derive(Clone, Copy, PartialEq)]
enum DivisionVariant {
    Division,
    Modulo,
}

fn slotted_codegen_division(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    ty: slotted_type_check::ast::Type,
    lhs: Box<slotted_type_check::ast::TypedExprNode>,
    rhs: Box<slotted_type_check::ast::TypedExprNode>,
    sign: crate::stage::slotted_type_check::ast::Signed,
    division_variant: DivisionVariant,
) -> Vec<String> {
    use crate::stage::slotted_type_check::ast::Signed;

    let width = slotted_operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_retval| {
        let lhs_ctx = slotted_codegen_expr(allocator, ret_val, *lhs);
        let rhs_ctx = slotted_codegen_expr(allocator, rhs_retval, *rhs);
        let operand_suffix = operator_suffix(width);

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![
                format!(
                    "\tmov{}\t%{}, %{}\n",
                    operand_suffix,
                    ret_val.fmt_with_operand_width(width),
                    ScalarRegister::A.fmt_with_operand_width(width)
                ),
                match sign {
                    Signed::Signed => format!(
                        "\tcqo\n\tidiv{}\t%{}\n",
                        operand_suffix,
                        rhs_retval.fmt_with_operand_width(width)
                    ),
                    Signed::Unsigned => {
                        let d_reg =
                            ScalarRegister::D.fmt_with_operand_width(OperandWidth::QuadWord);

                        format!(
                            "\txorq\t%{}, %{}\n\tdiv{}\t%{}\n",
                            d_reg,
                            d_reg,
                            operand_suffix,
                            rhs_retval.fmt_with_operand_width(width)
                        )
                    }
                },
                match division_variant {
                    DivisionVariant::Division => format!(
                        "\tmov{}\t%{}, %{}\n",
                        operand_suffix,
                        ScalarRegister::A.fmt_with_operand_width(width),
                        ret_val.fmt_with_operand_width(width)
                    ),
                    DivisionVariant::Modulo => format!(
                        "\tmov{}\t%{}, %{}\n",
                        operand_suffix,
                        ScalarRegister::D.fmt_with_operand_width(width),
                        ret_val.fmt_with_operand_width(width)
                    ),
                }
            ],
        )
    })
}

fn codegen_division(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    ty: ast::Type,
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
    sign: crate::stage::ast::Signed,
    division_variant: DivisionVariant,
) -> Vec<String> {
    use crate::stage::ast::Signed;

    let width = operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_retval| {
        let lhs_ctx = codegen_expr(allocator, ret_val, *lhs);
        let rhs_ctx = codegen_expr(allocator, rhs_retval, *rhs);
        let operand_suffix = operator_suffix(width);

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![
                format!(
                    "\tmov{}\t%{}, %{}\n",
                    operand_suffix,
                    ret_val.fmt_with_operand_width(width),
                    ScalarRegister::A.fmt_with_operand_width(width)
                ),
                match sign {
                    Signed::Signed => format!(
                        "\tcqo\n\tidiv{}\t%{}\n",
                        operand_suffix,
                        rhs_retval.fmt_with_operand_width(width)
                    ),
                    Signed::Unsigned => {
                        let d_reg =
                            ScalarRegister::D.fmt_with_operand_width(OperandWidth::QuadWord);

                        format!(
                            "\txorq\t%{}, %{}\n\tdiv{}\t%{}\n",
                            d_reg,
                            d_reg,
                            operand_suffix,
                            rhs_retval.fmt_with_operand_width(width)
                        )
                    }
                },
                match division_variant {
                    DivisionVariant::Division => format!(
                        "\tmov{}\t%{}, %{}\n",
                        operand_suffix,
                        ScalarRegister::A.fmt_with_operand_width(width),
                        ret_val.fmt_with_operand_width(width)
                    ),
                    DivisionVariant::Modulo => format!(
                        "\tmov{}\t%{}, %{}\n",
                        operand_suffix,
                        ScalarRegister::D.fmt_with_operand_width(width),
                        ret_val.fmt_with_operand_width(width)
                    ),
                }
            ],
        )
    })
}

// Binary

fn slotted_codegen_or(
    ty: slotted_type_check::ast::Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    lhs: slotted_type_check::ast::TypedExprNode,
    rhs: slotted_type_check::ast::TypedExprNode,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let rhs_ctx = slotted_codegen_expr(allocator, rhs_ret_val, rhs);
        let lhs_ctx = slotted_codegen_expr(allocator, ret_val, lhs);

        flattenable_instructions!(
            rhs_ctx,
            lhs_ctx,
            vec![format!(
                "\tor{}\t%{}, %{}\n",
                operator_suffix(width),
                rhs_ret_val.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        )
    })
}

fn codegen_or(
    ty: Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    lhs: ast::TypedExprNode,
    rhs: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let rhs_ctx = codegen_expr(allocator, rhs_ret_val, rhs);
        let lhs_ctx = codegen_expr(allocator, ret_val, lhs);

        flattenable_instructions!(
            rhs_ctx,
            lhs_ctx,
            vec![format!(
                "\tor{}\t%{}, %{}\n",
                operator_suffix(width),
                rhs_ret_val.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        )
    })
}

fn slotted_codegen_xor(
    ty: slotted_type_check::ast::Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    lhs: slotted_type_check::ast::TypedExprNode,
    rhs: slotted_type_check::ast::TypedExprNode,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let rhs_ctx = slotted_codegen_expr(allocator, rhs_ret_val, rhs);
        let lhs_ctx = slotted_codegen_expr(allocator, ret_val, lhs);

        flattenable_instructions!(
            rhs_ctx,
            lhs_ctx,
            vec![format!(
                "\txor{}\t%{}, %{}\n",
                operator_suffix(width),
                rhs_ret_val.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        )
    })
}

fn codegen_xor(
    ty: Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    lhs: ast::TypedExprNode,
    rhs: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let rhs_ctx = codegen_expr(allocator, rhs_ret_val, rhs);
        let lhs_ctx = codegen_expr(allocator, ret_val, lhs);

        flattenable_instructions!(
            rhs_ctx,
            lhs_ctx,
            vec![format!(
                "\txor{}\t%{}, %{}\n",
                operator_suffix(width),
                rhs_ret_val.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        )
    })
}

fn slotted_codegen_and(
    ty: slotted_type_check::ast::Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    lhs: slotted_type_check::ast::TypedExprNode,
    rhs: slotted_type_check::ast::TypedExprNode,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let rhs_ctx = slotted_codegen_expr(allocator, rhs_ret_val, rhs);
        let lhs_ctx = slotted_codegen_expr(allocator, ret_val, lhs);

        flattenable_instructions!(
            rhs_ctx,
            lhs_ctx,
            vec![format!(
                "\tand{}\t%{}, %{}\n",
                operator_suffix(width),
                rhs_ret_val.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        )
    })
}

fn codegen_and(
    ty: Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    lhs: ast::TypedExprNode,
    rhs: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let rhs_ctx = codegen_expr(allocator, rhs_ret_val, rhs);
        let lhs_ctx = codegen_expr(allocator, ret_val, lhs);

        flattenable_instructions!(
            rhs_ctx,
            lhs_ctx,
            vec![format!(
                "\tand{}\t%{}, %{}\n",
                operator_suffix(width),
                rhs_ret_val.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width)
            )],
        )
    })
}

fn slotted_codegen_shift_left(
    ty: slotted_type_check::ast::Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    lhs: slotted_type_check::ast::TypedExprNode,
    rhs: slotted_type_check::ast::TypedExprNode,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let rhs_ctx = slotted_codegen_expr(allocator, rhs_ret_val, rhs);
        let lhs_ctx = slotted_codegen_expr(allocator, ret_val, lhs);

        flattenable_instructions!(
            rhs_ctx,
            lhs_ctx,
            vec![
                format!(
                    "\tmov{}\t%{}, %cl\n",
                    operator_suffix(OperandWidth::Byte),
                    rhs_ret_val.fmt_with_operand_width(OperandWidth::Byte),
                ),
                format!(
                    "\tshl{}\t%cl, %{}\n",
                    operator_suffix(width),
                    ret_val.fmt_with_operand_width(width)
                )
            ],
        )
    })
}

fn codegen_shift_left(
    ty: Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    lhs: ast::TypedExprNode,
    rhs: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let rhs_ctx = codegen_expr(allocator, rhs_ret_val, rhs);
        let lhs_ctx = codegen_expr(allocator, ret_val, lhs);

        flattenable_instructions!(
            rhs_ctx,
            lhs_ctx,
            vec![
                format!(
                    "\tmov{}\t%{}, %cl\n",
                    operator_suffix(OperandWidth::Byte),
                    rhs_ret_val.fmt_with_operand_width(OperandWidth::Byte),
                ),
                format!(
                    "\tshl{}\t%cl, %{}\n",
                    operator_suffix(width),
                    ret_val.fmt_with_operand_width(width)
                )
            ],
        )
    })
}

fn slotted_codegen_shift_right(
    ty: slotted_type_check::ast::Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    lhs: slotted_type_check::ast::TypedExprNode,
    rhs: slotted_type_check::ast::TypedExprNode,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let rhs_ctx = slotted_codegen_expr(allocator, rhs_ret_val, rhs);
        let lhs_ctx = slotted_codegen_expr(allocator, ret_val, lhs);

        flattenable_instructions!(
            rhs_ctx,
            lhs_ctx,
            vec![
                format!(
                    "\tmov{}\t%{}, %cl\n",
                    operator_suffix(OperandWidth::Byte),
                    rhs_ret_val.fmt_with_operand_width(OperandWidth::Byte),
                ),
                format!(
                    "\tshr{}\t%cl, %{}\n",
                    operator_suffix(width),
                    ret_val.fmt_with_operand_width(width)
                )
            ],
        )
    })
}

fn codegen_shift_right(
    ty: Type,
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    lhs: ast::TypedExprNode,
    rhs: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, rhs_ret_val| {
        let rhs_ctx = codegen_expr(allocator, rhs_ret_val, rhs);
        let lhs_ctx = codegen_expr(allocator, ret_val, lhs);

        flattenable_instructions!(
            rhs_ctx,
            lhs_ctx,
            vec![
                format!(
                    "\tmov{}\t%{}, %cl\n",
                    operator_suffix(OperandWidth::Byte),
                    rhs_ret_val.fmt_with_operand_width(OperandWidth::Byte),
                ),
                format!(
                    "\tshr{}\t%cl, %{}\n",
                    operator_suffix(width),
                    ret_val.fmt_with_operand_width(width)
                )
            ],
        )
    })
}

/// Invert a register's value.
fn slotted_codegen_invert(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    expr: slotted_type_check::ast::TypedExprNode,
) -> Vec<String> {
    use crate::stage::slotted_type_check::ast::Typed;

    let width = slotted_operand_width_of_type(expr.r#type());
    let expr_ctx = slotted_codegen_expr(allocator, ret_val, expr);

    flattenable_instructions!(
        expr_ctx,
        vec![format!(
            "\tnot{}\t%{}\n",
            operator_suffix(width),
            ret_val.fmt_with_operand_width(width)
        )],
    )
}

/// Invert a register's value.
fn codegen_invert(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    expr: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(expr.r#type());
    let expr_ctx = codegen_expr(allocator, ret_val, expr);

    flattenable_instructions!(
        expr_ctx,
        vec![format!(
            "\tnot{}\t%{}\n",
            operator_suffix(width),
            ret_val.fmt_with_operand_width(width)
        )],
    )
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

fn slotted_codegen_compare_and_set(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    comparison_op: ComparisonOperation,
    ty: slotted_type_check::ast::Type,
    lhs: Box<slotted_type_check::ast::TypedExprNode>,
    rhs: Box<slotted_type_check::ast::TypedExprNode>,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, lhs_retval| {
        let lhs_ctx = slotted_codegen_expr(allocator, lhs_retval, *lhs);
        let rhs_ctx = slotted_codegen_expr(allocator, ret_val, *rhs);

        let set_operator = match comparison_op {
            ComparisonOperation::LessThan => "setl",
            ComparisonOperation::LessEqual => "setle",
            ComparisonOperation::GreaterThan => "setg",
            ComparisonOperation::GreaterEqual => "setge",
            ComparisonOperation::Equal => "sete",
            ComparisonOperation::NotEqual => "setne",
        };

        let operand_suffix = operator_suffix(width);

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![
                format!(
                    "\tcmp{}\t%{}, %{}\n",
                    operand_suffix,
                    ret_val.fmt_with_operand_width(width),
                    lhs_retval.fmt_with_operand_width(width)
                ),
                format!(
                    "\t{}\t%{}\n",
                    set_operator,
                    ret_val.fmt_with_operand_width(OperandWidth::Byte)
                ),
                format!(
                    "\tandq\t$255, %{}\n",
                    ret_val.fmt_with_operand_width(OperandWidth::QuadWord)
                ),
            ],
        )
    })
}

fn codegen_compare_and_set(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    comparison_op: ComparisonOperation,
    ty: ast::Type,
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
) -> Vec<String> {
    let width = operand_width_of_type(ty);

    allocator.allocate_gp_register_then(|allocator, lhs_retval| {
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

        let operand_suffix = operator_suffix(width);

        flattenable_instructions!(
            lhs_ctx,
            rhs_ctx,
            vec![
                format!(
                    "\tcmp{}\t%{}, %{}\n",
                    operand_suffix,
                    ret_val.fmt_with_operand_width(width),
                    lhs_retval.fmt_with_operand_width(width)
                ),
                format!(
                    "\t{}\t%{}\n",
                    set_operator,
                    ret_val.fmt_with_operand_width(OperandWidth::Byte)
                ),
                format!(
                    "\tandq\t$255, %{}\n",
                    ret_val.fmt_with_operand_width(OperandWidth::QuadWord)
                ),
            ],
        )
    })
}

fn codegen_compare_and_jmp<L>(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    cond_true_id: L,
    cond_false_id: L,
) -> Vec<String>
where
    L: LabelFormattable,
{
    const WIDTH: OperandWidth = OperandWidth::QuadWord;
    let operand_suffix = operator_suffix(WIDTH);
    allocator.allocate_gp_register_then(|_, zero_val| {
        vec![
            format!("\tandq\t$0, %{}\n", zero_val.fmt_with_operand_width(WIDTH)),
            format!(
                "\tcmp{}\t%{}, %{}\n",
                operand_suffix,
                ret_val.fmt_with_operand_width(WIDTH),
                zero_val.fmt_with_operand_width(WIDTH)
            ),
            format!(
                "\t{}\t%{}\n",
                "sete",
                ret_val.fmt_with_operand_width(OperandWidth::Byte)
            ),
            format!(
                "\tandq\t$255, %{}\n",
                ret_val.fmt_with_operand_width(OperandWidth::QuadWord)
            ),
            format!("\t{}\t{}\n", "je", cond_true_id),
        ]
        .into_iter()
        .chain(codegen_jump(cond_false_id).into_iter())
        .collect()
    })
}

// Unary

/// Negate a register's value.
fn slotted_codegen_negate(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    expr: slotted_type_check::ast::TypedExprNode,
) -> Vec<String> {
    use crate::stage::slotted_type_check::ast::Typed;

    let width = slotted_operand_width_of_type(expr.r#type());
    let expr_ctx = slotted_codegen_expr(allocator, ret_val, expr);

    flattenable_instructions!(
        expr_ctx,
        vec![format!(
            "\tneg{}\t%{}\n",
            operator_suffix(width),
            ret_val.fmt_with_operand_width(width)
        )],
    )
}

/// Negate a register's value.
fn codegen_negate(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    expr: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(expr.r#type());
    let expr_ctx = codegen_expr(allocator, ret_val, expr);

    flattenable_instructions!(
        expr_ctx,
        vec![format!(
            "\tneg{}\t%{}\n",
            operator_suffix(width),
            ret_val.fmt_with_operand_width(width)
        )],
    )
}

/// Logically negate a register's value.
fn slotted_codegen_not(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    expr: slotted_type_check::ast::TypedExprNode,
) -> Vec<String> {
    let expr_ctx = slotted_codegen_expr(allocator, ret_val, expr);
    let byte_ret_val_reg = ret_val.fmt_with_operand_width(OperandWidth::Byte);
    let quadword_ret_val_reg = ret_val.fmt_with_operand_width(OperandWidth::QuadWord);

    flattenable_instructions!(
        expr_ctx,
        vec![
            format!(
                "\ttestq\t%{width_adj_reg}, %{width_adj_reg}\n",
                width_adj_reg = quadword_ret_val_reg
            ),
            format!("\tsete\t%{}\n", byte_ret_val_reg),
            format!(
                "\tmovzbq\t%{}, %{}\n",
                byte_ret_val_reg, quadword_ret_val_reg
            )
        ],
    )
}

/// Logically negate a register's value.
fn codegen_not(
    allocator: &mut SysVAllocator,
    ret_val: &GeneralPurposeRegister,
    expr: ast::TypedExprNode,
) -> Vec<String> {
    let expr_ctx = codegen_expr(allocator, ret_val, expr);
    let byte_ret_val_reg = ret_val.fmt_with_operand_width(OperandWidth::Byte);
    let quadword_ret_val_reg = ret_val.fmt_with_operand_width(OperandWidth::QuadWord);

    flattenable_instructions!(
        expr_ctx,
        vec![
            format!(
                "\ttestq\t%{width_adj_reg}, %{width_adj_reg}\n",
                width_adj_reg = quadword_ret_val_reg
            ),
            format!("\tsete\t%{}\n", byte_ret_val_reg),
            format!(
                "\tmovzbq\t%{}, %{}\n",
                byte_ret_val_reg, quadword_ret_val_reg
            )
        ],
    )
}

fn slotted_codegen_call(
    allocator: &mut SysVAllocator,
    ty: slotted_type_check::ast::Type,
    ret_val: &GeneralPurposeRegister,
    func_name: &str,
    arg: Option<Box<slotted_type_check::ast::TypedExprNode>>,
) -> Vec<String> {
    use slotted_type_check::ast::Typed;

    let width = slotted_operand_width_of_type(ty);
    if let Some(arg_expr) = arg {
        let width = slotted_operand_width_of_type(arg_expr.r#type());

        allocator.allocate_gp_register_then(|allocator, arg_retval| {
            let arg_ctx = slotted_codegen_expr(allocator, arg_retval, *arg_expr);

            flattenable_instructions!(
                arg_ctx,
                vec![
                    format!(
                        "\tmov{}\t%{}, %{}\n",
                        operator_suffix(width),
                        arg_retval.fmt_with_operand_width(width),
                        ScalarRegister::D.fmt_with_operand_width(width)
                    ),
                    format!("\tcall\t{}\n", func_name),
                    format!(
                        "\tmov{}\t%{}, {}\n",
                        operator_suffix(width),
                        ScalarRegister::A.fmt_with_operand_width(width),
                        ret_val.fmt_with_operand_width(width),
                    ),
                ],
            )
        })
    } else {
        vec![
            format!("\tcall\t{}\n", func_name),
            format!(
                "\tmov{}\t%{}, %{}\n",
                operator_suffix(width),
                ScalarRegister::A.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width),
            ),
        ]
    }
}

fn codegen_call(
    allocator: &mut SysVAllocator,
    ty: Type,
    ret_val: &GeneralPurposeRegister,
    func_name: &str,
    arg: Option<Box<ast::TypedExprNode>>,
) -> Vec<String> {
    let width = operand_width_of_type(ty);
    if let Some(arg_expr) = arg {
        let width = operand_width_of_type(arg_expr.r#type());

        allocator.allocate_gp_register_then(|allocator, arg_retval| {
            let arg_ctx = codegen_expr(allocator, arg_retval, *arg_expr);

            flattenable_instructions!(
                arg_ctx,
                vec![
                    format!(
                        "\tmov{}\t%{}, %{}\n",
                        operator_suffix(width),
                        arg_retval.fmt_with_operand_width(width),
                        ScalarRegister::D.fmt_with_operand_width(width)
                    ),
                    format!("\tcall\t{}\n", func_name),
                    format!(
                        "\tmov{}\t%{}, {}\n",
                        operator_suffix(width),
                        ScalarRegister::A.fmt_with_operand_width(width),
                        ret_val.fmt_with_operand_width(width),
                    ),
                ],
            )
        })
    } else {
        vec![
            format!("\tcall\t{}\n", func_name),
            format!(
                "\tmov{}\t%{}, %{}\n",
                operator_suffix(width),
                ScalarRegister::A.fmt_with_operand_width(width),
                ret_val.fmt_with_operand_width(width),
            ),
        ]
    }
}

fn slotted_codegen_return(
    ty: slotted_type_check::ast::Type,
    ret_val: &GeneralPurposeRegister,
    func_name: &str,
) -> Vec<String> {
    let width = slotted_operand_width_of_type(ty);
    vec![format!(
        "\tmov{}\t%{}, %{}\n",
        operator_suffix(width),
        ret_val.fmt_with_operand_width(width),
        ScalarRegister::A.fmt_with_operand_width(width)
    )]
    .into_iter()
    .chain(codegen_jump(format!("func_{}_ret", func_name)).into_iter())
    .collect()
}

fn codegen_return(ty: Type, ret_val: &GeneralPurposeRegister, func_name: &str) -> Vec<String> {
    let width = operand_width_of_type(ty);
    vec![format!(
        "\tmov{}\t%{}, %{}\n",
        operator_suffix(width),
        ret_val.fmt_with_operand_width(width),
        ScalarRegister::A.fmt_with_operand_width(width)
    )]
    .into_iter()
    .chain(codegen_jump(format!("func_{}_ret", func_name)).into_iter())
    .collect()
}

const fn operator_suffix(width: OperandWidth) -> &'static str {
    match width {
        OperandWidth::QuadWord => "q",
        OperandWidth::DoubleWord => "l",
        OperandWidth::Word => "w",
        OperandWidth::Byte => "b",
    }
}

fn operand_width_of_type(ty: Type) -> OperandWidth {
    match ty {
        Type::Integer(_, iw) => match iw {
            ast::IntegerWidth::One | ast::IntegerWidth::Eight => OperandWidth::Byte,
            ast::IntegerWidth::Sixteen => OperandWidth::Word,
            ast::IntegerWidth::ThirtyTwo => OperandWidth::DoubleWord,
            ast::IntegerWidth::SixtyFour => OperandWidth::QuadWord,
        },
        Type::Void | Type::Func(_) | Type::Pointer(_) => OperandWidth::QuadWord,
    }
}

fn slotted_operand_width_of_type(ty: slotted_type_check::ast::Type) -> OperandWidth {
    use slotted_type_check::ast;
    use slotted_type_check::ast::Type;
    match ty {
        Type::Integer(_, iw) => match iw {
            ast::IntegerWidth::One | ast::IntegerWidth::Eight => OperandWidth::Byte,
            ast::IntegerWidth::Sixteen => OperandWidth::Word,
            ast::IntegerWidth::ThirtyTwo => OperandWidth::DoubleWord,
            ast::IntegerWidth::SixtyFour => OperandWidth::QuadWord,
        },
        Type::Void | Type::Func(_) | Type::Pointer(_) => OperandWidth::QuadWord,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stage::ast;

    macro_rules! compound_statements {
        ($($stmt:expr,)*) => {
               $crate::stage::ast::TypedCompoundStmts::new(
                   vec![
                    $(
                        $stmt,
                    )*
                   ]
               )

        };
    }

    macro_rules! pad_to_le_64bit_array {
        ($val:literal) => {
            $crate::util::pad_to_64bit_array($val.to_le_bytes())
        };
    }

    #[test]
    fn should_use_correct_return_register_for_modulo_operations() {
        use crate::stage::CompilationStage;
        use ast::{IntegerWidth, Primary, Signed, TypedExprNode, TypedStmtNode};

        let modulo_expr_stmt = TypedStmtNode::Expression(TypedExprNode::Modulo(
            generate_type_specifier!(u8),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u8),
                Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(10u8),
                },
            )),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u8),
                Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(3u8),
                },
            )),
        ));

        let div_expr_stmt = TypedStmtNode::Expression(TypedExprNode::Division(
            generate_type_specifier!(u8),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u8),
                Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(10u8),
                },
            )),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u8),
                Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(3u8),
                },
            )),
        ));

        assert_eq!(
            Ok(vec![
                "\tmovq\t$10, %r15
\tmovq\t$3, %r14
\tmovb\t%r15b, %al
\txorq\t%rdx, %rdx
\tdivb\t%r14b
\tmovb\t%dl, %r15b
"
                .to_string(),
                "\tmovq\t$10, %r13
\tmovq\t$3, %r12
\tmovb\t%r13b, %al
\txorq\t%rdx, %rdx
\tdivb\t%r12b
\tmovb\t%al, %r13b
"
                .to_string()
            ]),
            X86_64.apply(compound_statements!(modulo_expr_stmt, div_expr_stmt,))
        );
    }

    #[test]
    fn should_scale_on_array_deref() {
        use crate::stage::CompilationStage;
        use ast::{
            IdentifierLocality, IntegerWidth, Primary, Signed, TypedExprNode, TypedStmtNode,
        };

        let index_expression = TypedStmtNode::Expression(ast::TypedExprNode::Deref(
            generate_type_specifier!(u8),
            Box::new(ast::TypedExprNode::Addition(
                generate_type_specifier!(u8).pointer_to(),
                Box::new(ast::TypedExprNode::Ref(
                    generate_type_specifier!(u8),
                    IdentifierLocality::Global("x".to_string()),
                )),
                Box::new(TypedExprNode::ScaleBy(
                    generate_type_specifier!(u8),
                    Box::new(TypedExprNode::Grouping(
                        generate_type_specifier!(u64),
                        Box::new(TypedExprNode::Primary(
                            generate_type_specifier!(u8),
                            Primary::Integer {
                                sign: Signed::Unsigned,
                                width: IntegerWidth::Eight,
                                value: pad_to_le_64bit_array!(1u8),
                            },
                        )),
                    )),
                )),
            )),
        ));

        assert_eq!(
            Ok(vec!["\tleaq\tx(%rip), %r14
\tmovq\t$1, %r13
\tmovq\t$1, %r15
\timulq\t%r13, %r15
\taddq\t%r14, %r15
\tmovb\t(%r15), %r15b
"
            .to_string()]),
            X86_64.apply(compound_statements!(index_expression,))
        );
    }
}
