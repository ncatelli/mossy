use crate::stage::codegen::machine::arch::TargetArchitecture;
use crate::stage::codegen::{self, CodeGenerationErr};

use crate::stage::type_check::ast::{self, ByteSized, Type, Typed};
use crate::stage::CompilationStage;
use core::sync::atomic::{AtomicUsize, Ordering};

static BLOCK_ID: AtomicUsize = AtomicUsize::new(0);

mod allocator;
use allocator::{
    register::{
        BasePointerRegister, GPRegisterAllocator, GeneralPurposeRegister, IntegerRegister,
        OperandWidth, PointerRegister, WidthFormatted,
    },
    RegisterOrOffset, SysVAllocator,
};

/// Operand represents a type that can be used as a return value register.
/// Typically this will be either a register or memory offset.
trait Operand: WidthFormatted + Copy {}

impl Operand for GeneralPurposeRegister {}
impl Operand for &GeneralPurposeRegister {}
impl Operand for IntegerRegister {}

impl<GP> Operand for allocator::RegisterOrOffset<GP>
where
    GP: WidthFormatted,
    Self: WidthFormatted + Copy,
{
}

impl<GP> Operand for &allocator::RegisterOrOffset<GP>
where
    GP: WidthFormatted,
    Self: WidthFormatted + Copy,
{
}

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

impl CompilationStage<ast::TypedFunctionDeclaration, Vec<String>, CodeGenerationErr> for X86_64 {
    fn apply(
        &mut self,
        input: ast::TypedFunctionDeclaration,
    ) -> Result<Vec<String>, CodeGenerationErr> {
        let mut allocator = SysVAllocator::new(GPRegisterAllocator::default());
        allocator.allocate_new_local_stack_scope(|allocator| {
            let (id, block) = (input.id, input.block);
            let parameters = input.parameters;

            for (slot, param) in parameters.iter().enumerate() {
                allocator.calculate_and_insert_parameter_offset(slot, param);
            }

            codegen_statements(allocator, block)
                .map(|block| {
                    let last = allocator.top_of_local_stack();

                    let alignment = allocator.align_stack_pointer(last);
                    vec![
                        codegen_function_preamble(allocator, &id, &parameters, alignment),
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

fn codegen_statement(
    allocator: &mut SysVAllocator,
    input: ast::TypedStmtNode,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    match input {
        ast::TypedStmtNode::Expression(expr) => {
            allocator.allocate_general_purpose_register_then(|allocator, ret| {
                Ok(vec![codegen_expr(allocator, ret, expr)])
            })
        }
        ast::TypedStmtNode::LocalDeclaration(dec, slot_ids) => {
            match dec {
                ast::Declaration::Scalar(ty, _) => {
                    for slot in slot_ids {
                        allocator.calculate_and_insert_local_offset(slot, ty.clone());
                    }
                }
                ast::Declaration::Array { ty, size, .. } => {
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
        ast::TypedStmtNode::Return(ty, id, arg) => allocator
            .allocate_general_purpose_register_then(|allocator, ret| {
                let res: Vec<String> = if let Some(expr) = arg {
                    codegen_expr(allocator, ret, expr)
                } else {
                    vec![]
                }
                .into_iter()
                .chain(codegen_return(ty, ret, &id))
                .collect();

                Ok(vec![res])
            }),

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

fn codegen_if_statement_with_else(
    allocator: &mut SysVAllocator,
    cond: ast::TypedExprNode,
    true_case: ast::TypedCompoundStmts,
    false_case: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_general_purpose_register_then(|allocator, ret| {
        allocator.allocate_general_purpose_register_then(|allocator, cond_expr_ret| {
            let cond_expr_ty = cond.r#type();
            let cond_ctx = codegen_expr(allocator, cond_expr_ret, cond);
            let exit_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
            let true_case_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
            let tctx = codegen_statements(allocator, true_case)?;
            let else_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
            let block_ctx = codegen_statements(allocator, false_case)?;

            Ok(flattenable_instructions!(
                cond_ctx,
                vec![format!(
                    "\tand{}\t$0, {}\n",
                    operator_suffix(OperandWidth::QuadWord),
                    ret.fmt_with_operand_width(OperandWidth::QuadWord)
                )],
                codegen_mov(cond_expr_ty, cond_expr_ret, ret),
                codegen_compare_and_jmp(
                    allocator,
                    ret,
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
    })
}

fn codegen_if_statement_without_else(
    allocator: &mut SysVAllocator,
    cond: ast::TypedExprNode,
    true_case: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_general_purpose_register_then(|allocator, ret| {
        allocator.allocate_general_purpose_register_then(|allocator, cond_expr_ret| {
            let cond_expr_ty = cond.r#type();
            let cond_ctx = codegen_expr(allocator, cond_expr_ret, cond);
            let exit_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
            let true_case_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
            let tctx = codegen_statements(allocator, true_case)?;

            Ok(flattenable_instructions!(
                cond_ctx,
                vec![format!(
                    "\tand{}\t$0, {}\n",
                    operator_suffix(OperandWidth::QuadWord),
                    ret.fmt_with_operand_width(OperandWidth::QuadWord)
                )],
                codegen_mov(cond_expr_ty, cond_expr_ret, ret),
                codegen_compare_and_jmp(
                    allocator,
                    ret,
                    LLabelPrefix(true_case_block_id),
                    LLabelPrefix(exit_block_id)
                ),
                codegen_label(LLabelPrefix(true_case_block_id)),
                tctx,
                codegen_label(LLabelPrefix(exit_block_id)),
            ))
        })
    })
}

fn codegen_while_statement(
    allocator: &mut SysVAllocator,
    cond: ast::TypedExprNode,
    block: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_general_purpose_register_then(|allocator, ret| {
        allocator.allocate_general_purpose_register_then(|allocator, cond_expr_ret_val| {
            let cond_expr_ty = cond.r#type();
            let cond_ctx = codegen_expr(allocator, cond_expr_ret_val, cond);
            let loop_cond_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
            let loop_start_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
            let loop_end_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
            let block_insts = codegen_statements(allocator, block)?;

            Ok(flattenable_instructions!(
                codegen_label(LLabelPrefix(loop_cond_block_id)),
                cond_ctx,
                vec![format!(
                    "\tand{}\t$0, {}\n",
                    operator_suffix(OperandWidth::QuadWord),
                    ret.fmt_with_operand_width(OperandWidth::QuadWord)
                )],
                codegen_mov(cond_expr_ty, cond_expr_ret_val, ret),
                codegen_compare_and_jmp(
                    allocator,
                    ret,
                    LLabelPrefix(loop_start_block_id),
                    LLabelPrefix(loop_end_block_id)
                ),
                codegen_label(LLabelPrefix(loop_start_block_id)),
                block_insts,
                codegen_jump(LLabelPrefix(loop_cond_block_id)),
                codegen_label(LLabelPrefix(loop_end_block_id)),
            ))
        })
    })
}

fn codegen_for_statement(
    allocator: &mut SysVAllocator,
    preop: ast::TypedStmtNode,
    cond: ast::TypedExprNode,
    postop: ast::TypedStmtNode,
    block: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_general_purpose_register_then(|allocator, ret| {
        allocator.allocate_general_purpose_register_then(|allocator, cond_expr_ret_val| {
            let preop_ctx = codegen_statement(allocator, preop)?;
            let cond_expr_ty = cond.r#type();
            let cond_ctx = codegen_expr(allocator, cond_expr_ret_val, cond);
            let postop_ctx = codegen_statement(allocator, postop)?;
            let loop_cond_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
            let loop_start_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
            let loop_end_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
            let block_insts = codegen_statements(allocator, block)?;

            Ok(flattenable_instructions!(
                preop_ctx,
                codegen_label(LLabelPrefix(loop_cond_block_id)),
                cond_ctx,
                vec![format!(
                    "\tand{}\t$0, {}\n",
                    operator_suffix(OperandWidth::QuadWord),
                    ret.fmt_with_operand_width(OperandWidth::QuadWord)
                )],
                codegen_mov(cond_expr_ty, cond_expr_ret_val, ret),
                codegen_compare_and_jmp(
                    allocator,
                    ret,
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
    })
}

fn codegen_function_preamble(
    allocator: &mut SysVAllocator,
    identifier: &str,
    parameters: &[Type],
    alignment: isize,
) -> Vec<String> {
    let param_cnt = allocator.parameter_stack_offsets.len();
    let src_to_dst_param_mapping = (0..param_cnt)
        .into_iter()
        .flat_map(|slot| {
            let src_reg = allocator.parameter_passing_register_for_slot(slot);
            allocator
                .get_parameter_slot_offset(slot)
                .map(|dst_offset| (src_reg, dst_offset, parameters[slot].clone()))
        })
        .flat_map(|(src, dst_offset, ty)| {
            let width = operand_width_of_type(ty);
            vec![format!(
                "\tmov{}\t{}, {}({})\n",
                operator_suffix(width),
                src.fmt_with_operand_width(width),
                dst_offset,
                BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
            )]
        })
        .collect();

    flattenable_instructions!(
        vec![format!(
            "\t.text
\t.globl\t{name}
\t.type\t{name}, @function
{name}:
\tpushq\t%rbp
\tmovq\t%rsp, %rbp
\tsubq\t${alignment}, %rsp\n",
            name = identifier,
            alignment = alignment
        )],
        src_to_dst_param_mapping,
    )
}

fn codegen_function_postamble(identifier: &str, alignment: isize) -> Vec<String> {
    codegen_label(format!("func_{}_ret", identifier))
        .into_iter()
        .chain(
            vec![format!(
                "\taddq\t${}, %rsp
\tpopq\t%rbp
\tret\n\n",
                alignment
            )]
            .into_iter(),
        )
        .collect()
}

fn codegen_global_symbol(ty: &ast::Type, identifier: &str, count: usize) -> Vec<String> {
    let reserve_bytes = ty.size() * count;

    vec![format!(
        "\t.data\n\t.globl\t{}\n{}:\n\t.zero\t{}\n\t.text\n",
        identifier, identifier, reserve_bytes
    )]
}

fn codegen_store_global(
    ty: ast::Type,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    identifier: &str,
) -> Vec<String> {
    let width = operand_width_of_type(ty);
    vec![format!(
        "\tmov{}\t{}, {}({})\n",
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

fn codegen_store_local(
    ty: ast::Type,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    offset: isize,
) -> Vec<String> {
    let width = operand_width_of_type(ty);
    vec![format!(
        "\tmov{}\t{}, {}({})\n",
        operator_suffix(width),
        ret.fmt_with_operand_width(width),
        offset,
        BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
    )]
}

fn codegen_load_local(
    ty: ast::Type,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    offset: isize,
    scale: usize,
) -> Vec<String> {
    let scale_by = -((ty.size() * scale) as isize);
    let scaled_offset = offset + scale_by;

    *ret = RegisterOrOffset::Offset(scaled_offset);
    vec![]
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IncDecExpression {
    PreIncrement,
    PreDecrement,
    PostIncrement,
    PostDecrement,
}

fn codegen_inc_or_dec_expression_from_identifier(
    ty: ast::Type,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    identifier: &str,
    expr_op: IncDecExpression,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    let op = match expr_op {
        IncDecExpression::PreIncrement | IncDecExpression::PostIncrement => format!(
            "\tinc{}\t{}({})\n",
            operator_suffix(width),
            identifier,
            PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ),
        IncDecExpression::PreDecrement | IncDecExpression::PostDecrement => format!(
            "\tdec{}\t{}({})\n",
            operator_suffix(width),
            identifier,
            PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ),
    };

    match expr_op {
        IncDecExpression::PreIncrement | IncDecExpression::PreDecrement => {
            flattenable_instructions!(vec![op], codegen_load_global(ty, ret, identifier, 0),)
        }
        IncDecExpression::PostIncrement | IncDecExpression::PostDecrement => {
            flattenable_instructions!(codegen_load_global(ty, ret, identifier, 0), vec![op],)
        }
    }
}

fn codegen_inc_or_dec_expression_from_local_offset(
    ty: ast::Type,
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    offset: isize,
    expr_op: IncDecExpression,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    let op = match expr_op {
        IncDecExpression::PreIncrement | IncDecExpression::PostIncrement => format!(
            "\tinc{}\t{}({})\n",
            operator_suffix(width),
            offset,
            BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ),
        IncDecExpression::PreDecrement | IncDecExpression::PostDecrement => format!(
            "\tdec{}\t{}({})\n",
            operator_suffix(width),
            offset,
            BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ),
    };

    match expr_op {
        IncDecExpression::PreIncrement | IncDecExpression::PreDecrement => {
            flattenable_instructions!(vec![op], codegen_load_local(ty, ret, offset, 0),)
        }
        IncDecExpression::PostIncrement | IncDecExpression::PostDecrement => allocator
            .allocate_general_purpose_register_then(|_, post_inc_op_reg| {
                flattenable_instructions!(
                    codegen_load_local(ty.clone(), post_inc_op_reg, offset, 0),
                    codegen_mov(ty, post_inc_op_reg, ret),
                    vec![op],
                )
            }),
    }
}

fn codegen_inc_or_dec_expression_from_pointer(
    ty: ast::Type,
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    expr_op: IncDecExpression,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    allocator.allocate_general_purpose_register_then(|_, ptr_reg| {
        let op = match expr_op {
            IncDecExpression::PreIncrement | IncDecExpression::PostIncrement => format!(
                "\tinc{}\t({})\n",
                operator_suffix(width),
                ptr_reg.fmt_with_operand_width(OperandWidth::QuadWord),
            ),
            IncDecExpression::PreDecrement | IncDecExpression::PostDecrement => format!(
                "\tdec{}\t({})\n",
                operator_suffix(width),
                ptr_reg.fmt_with_operand_width(OperandWidth::QuadWord),
            ),
        };

        match expr_op {
            IncDecExpression::PreIncrement | IncDecExpression::PreDecrement => {
                flattenable_instructions!(
                    codegen_mov_with_explicit_width(OperandWidth::QuadWord, ret, ptr_reg),
                    vec![op],
                    codegen_deref(ty, ret, 0),
                )
            }
            IncDecExpression::PostIncrement | IncDecExpression::PostDecrement => {
                flattenable_instructions!(
                    codegen_mov_with_explicit_width(OperandWidth::QuadWord, ret, ptr_reg),
                    codegen_deref(ty, ret, 0),
                    vec![op],
                )
            }
        }
    })
}

fn codegen_load_global(
    ty: ast::Type,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    identifier: &str,
    scale: usize,
) -> Vec<String> {
    let scale_by = ty.size() * scale;
    let width = operand_width_of_type(ty);

    if scale == 0 {
        vec![format!(
            "\tmov{}\t{}({}), {}\n",
            operator_suffix(width),
            identifier,
            PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    } else {
        vec![format!(
            "\tmov{}\t{}+{}({}), {}\n",
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

fn codegen_expr(
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    expr: ast::TypedExprNode,
) -> Vec<String> {
    use crate::stage::type_check::ast::{IntegerWidth, Primary, Signed, TypedExprNode};

    match expr {
        TypedExprNode::Primary(_, Primary::Integer { sign, width, value }) => match (sign, width) {
            (_, IntegerWidth::One) => {
                let boolean_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 8-bit integer");
                codegen_constant_u8(ret, boolean_literal)
            }

            (Signed::Signed, IntegerWidth::Eight) => {
                let signed_literal = u64::from_le_bytes(value);
                if signed_literal.leading_zeros() >= 56 {
                    codegen_constant_i8(ret, signed_literal as i8)
                } else {
                    panic!("value exceeds signed 8-bit integer")
                }
            }
            (Signed::Signed, IntegerWidth::Sixteen) => {
                let signed_literal = u64::from_le_bytes(value);
                if signed_literal.leading_zeros() >= 48 {
                    codegen_constant_i16(ret, signed_literal as i16)
                } else {
                    panic!("value exceeds signed 16-bit integer")
                }
            }
            (Signed::Signed, IntegerWidth::ThirtyTwo) => {
                let signed_literal = u64::from_le_bytes(value);
                if signed_literal.leading_zeros() >= 32 {
                    codegen_constant_i32(ret, signed_literal as i32)
                } else {
                    panic!("value exceeds signed 32-bit integer")
                }
            }
            (Signed::Signed, IntegerWidth::SixtyFour) => {
                codegen_constant_i64(ret, i64::from_le_bytes(value))
            }
            (Signed::Unsigned, IntegerWidth::Eight) => {
                let unsigned_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 8-bit integer");
                codegen_constant_u8(ret, unsigned_literal)
            }
            (Signed::Unsigned, IntegerWidth::Sixteen) => {
                let unsigned_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 32-bit integer");
                codegen_constant_u16(ret, unsigned_literal)
            }
            (Signed::Unsigned, IntegerWidth::ThirtyTwo) => {
                let unsigned_literal = core::convert::TryFrom::try_from(u64::from_le_bytes(value))
                    .expect("value exceeds unsigned 32-bit integer");
                codegen_constant_u32(ret, unsigned_literal)
            }
            (Signed::Unsigned, IntegerWidth::SixtyFour) => {
                codegen_constant_u64(ret, u64::from_le_bytes(value))
            }
        },

        TypedExprNode::Primary(ty, Primary::Identifier(_, ast::IdentifierLocality::Global(id))) => {
            codegen_load_global(ty, ret, &id, 0)
        }
        TypedExprNode::Primary(
            ty,
            Primary::Identifier(_, ast::IdentifierLocality::Local(slot)),
        ) => allocator
            .get_local_slot_offset(slot)
            .map(|offset_start| codegen_load_local(ty, ret, offset_start, 0))
            .expect("local stack slot is undeclared"),
        TypedExprNode::Primary(
            ty,
            Primary::Identifier(_, ast::IdentifierLocality::Parameter(slot)),
        ) => allocator
            .get_parameter_slot_offset(slot)
            .map(|offset_start| codegen_load_local(ty, ret, offset_start, 0))
            .expect("local parameter stack slot is undeclared"),
        TypedExprNode::Primary(_, Primary::Str(lit)) => {
            let identifier = format!("V{}", BLOCK_ID.fetch_add(1, Ordering::SeqCst));

            flattenable_instructions!(
                codegen_global_str(&identifier, &lit),
                codegen_reference_from_identifier(ret, &identifier),
            )
        }

        TypedExprNode::FunctionCall(ty, func_name, optional_arg) => {
            codegen_call(allocator, ty, ret, &func_name, optional_arg)
        }

        ast::TypedExprNode::IdentifierAssignment(
            ty,
            ast::IdentifierLocality::Global(identifier),
            expr,
        ) => allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
            flattenable_instructions!(
                codegen_expr(allocator, rhs_ret, *expr),
                codegen_mov(ty.clone(), rhs_ret, ret),
                codegen_store_global(ty, ret, &identifier),
            )
        }),
        ast::TypedExprNode::IdentifierAssignment(
            ty,
            ast::IdentifierLocality::Local(slot),
            expr,
        ) => allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
            flattenable_instructions!(
                codegen_expr(allocator, rhs_ret, *expr),
                codegen_mov(ty.clone(), rhs_ret, ret),
                allocator
                    .get_local_slot_offset(slot)
                    .map(|offset_start| { codegen_store_local(ty, ret, offset_start) })
                    .expect("local stack slot is undeclared"),
            )
        }),
        ast::TypedExprNode::IdentifierAssignment(
            ty,
            ast::IdentifierLocality::Parameter(slot),
            expr,
        ) => allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
            flattenable_instructions!(
                codegen_expr(allocator, rhs_ret, *expr),
                codegen_mov(ty.clone(), rhs_ret, ret),
                allocator
                    .get_parameter_slot_offset(slot)
                    .map(|offset_start| { codegen_store_local(ty, ret, offset_start) })
                    .expect("local parameter stack slot is undeclared"),
            )
        }),
        TypedExprNode::DerefAssignment(ty, lhs, rhs) => allocator
            .allocate_general_purpose_register_then(|allocator, rhs_ret| {
                flattenable_instructions!(
                    codegen_expr(allocator, rhs_ret, *rhs),
                    codegen_expr(allocator, ret, *lhs),
                    codegen_store_deref(ty, ret, rhs_ret),
                )
            }),

        TypedExprNode::LogOr(_, lhs, rhs) => {
            let ty = generate_type_specifier!(u64);
            codegen_or(ty, allocator, ret, *lhs, *rhs)
        }
        TypedExprNode::LogAnd(_, lhs, rhs) => {
            let ty = generate_type_specifier!(u64);
            codegen_and(ty, allocator, ret, *lhs, *rhs)
        }

        TypedExprNode::BitOr(ty, lhs, rhs) => codegen_or(ty, allocator, ret, *lhs, *rhs),
        TypedExprNode::BitXor(ty, lhs, rhs) => codegen_xor(ty, allocator, ret, *lhs, *rhs),
        TypedExprNode::BitAnd(ty, lhs, rhs) => codegen_and(ty, allocator, ret, *lhs, *rhs),

        TypedExprNode::Equal(ty, lhs, rhs) => {
            codegen_compare_and_set(allocator, ret, ComparisonOperation::Equal, ty, lhs, rhs)
        }
        TypedExprNode::NotEqual(ty, lhs, rhs) => {
            codegen_compare_and_set(allocator, ret, ComparisonOperation::NotEqual, ty, lhs, rhs)
        }
        TypedExprNode::LessThan(ty, lhs, rhs) => {
            codegen_compare_and_set(allocator, ret, ComparisonOperation::LessThan, ty, lhs, rhs)
        }
        TypedExprNode::GreaterThan(ty, lhs, rhs) => codegen_compare_and_set(
            allocator,
            ret,
            ComparisonOperation::GreaterThan,
            ty,
            lhs,
            rhs,
        ),
        TypedExprNode::LessEqual(ty, lhs, rhs) => {
            codegen_compare_and_set(allocator, ret, ComparisonOperation::LessEqual, ty, lhs, rhs)
        }
        TypedExprNode::GreaterEqual(ty, lhs, rhs) => codegen_compare_and_set(
            allocator,
            ret,
            ComparisonOperation::GreaterEqual,
            ty,
            lhs,
            rhs,
        ),

        TypedExprNode::BitShiftLeft(ty, lhs, rhs) => {
            codegen_shift_left(ty, allocator, ret, *lhs, *rhs)
        }
        TypedExprNode::BitShiftRight(ty, lhs, rhs) => {
            codegen_shift_right(ty, allocator, ret, *lhs, *rhs)
        }

        TypedExprNode::Addition(ast::Type::Pointer(ty), lhs, rhs) => {
            codegen_addition(allocator, ret, ty.pointer_to(), lhs, rhs)
        }
        TypedExprNode::Addition(ty, lhs, rhs) => codegen_addition(allocator, ret, ty, lhs, rhs),
        TypedExprNode::Subtraction(ty, lhs, rhs) => {
            codegen_subtraction(allocator, ret, ty, lhs, rhs)
        }
        TypedExprNode::Multiplication(ty, lhs, rhs) => {
            codegen_multiplication(allocator, ret, ty, lhs, rhs)
        }
        TypedExprNode::Division(ty, lhs, rhs) => codegen_division(
            allocator,
            ret,
            ty,
            lhs,
            rhs,
            Signed::Unsigned,
            DivisionVariant::Division,
        ),
        TypedExprNode::Modulo(ty, lhs, rhs) => codegen_division(
            allocator,
            ret,
            ty,
            lhs,
            rhs,
            Signed::Unsigned,
            DivisionVariant::Modulo,
        ),

        TypedExprNode::LogicalNot(_, expr) => codegen_not(allocator, ret, *expr),
        TypedExprNode::Negate(_, expr) => codegen_negate(allocator, ret, *expr),
        TypedExprNode::Invert(_, expr) => codegen_invert(allocator, ret, *expr),

        TypedExprNode::PreIncrement(_, expr) => match *expr {
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Global(identifier)),
            ) => codegen_inc_or_dec_expression_from_identifier(
                ty,
                ret,
                &identifier,
                IncDecExpression::PreIncrement,
            ),
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Local(slot)),
            ) => allocator
                .get_local_slot_offset(slot)
                .map(|offset_start| {
                    codegen_inc_or_dec_expression_from_local_offset(
                        ty,
                        allocator,
                        ret,
                        offset_start,
                        IncDecExpression::PreIncrement,
                    )
                })
                .expect("local stack slot is undeclared"),
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Parameter(slot)),
            ) => allocator
                .get_parameter_slot_offset(slot)
                .map(|offset_start| {
                    codegen_inc_or_dec_expression_from_local_offset(
                        ty,
                        allocator,
                        ret,
                        offset_start,
                        IncDecExpression::PreIncrement,
                    )
                })
                .expect("local parameter stack slot is undeclared"),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    codegen_expr(allocator, ret, *expr),
                    codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret,
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
                ret,
                &identifier,
                IncDecExpression::PreDecrement,
            ),
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Local(slot)),
            ) => allocator
                .get_local_slot_offset(slot)
                .map(|offset_start| {
                    codegen_inc_or_dec_expression_from_local_offset(
                        ty,
                        allocator,
                        ret,
                        offset_start,
                        IncDecExpression::PreDecrement,
                    )
                })
                .expect("local stack slot is undeclared"),
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Parameter(slot)),
            ) => allocator
                .get_parameter_slot_offset(slot)
                .map(|offset_start| {
                    codegen_inc_or_dec_expression_from_local_offset(
                        ty,
                        allocator,
                        ret,
                        offset_start,
                        IncDecExpression::PreDecrement,
                    )
                })
                .expect("local stack slot is undeclared"),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    codegen_expr(allocator, ret, *expr),
                    codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret,
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
                ret,
                &identifier,
                IncDecExpression::PostIncrement,
            ),
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Local(slot)),
            ) => allocator
                .get_local_slot_offset(slot)
                .map(|offset_start| {
                    codegen_inc_or_dec_expression_from_local_offset(
                        ty,
                        allocator,
                        ret,
                        offset_start,
                        IncDecExpression::PostIncrement,
                    )
                })
                .expect("local stack slot is undeclared"),
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Parameter(slot)),
            ) => allocator
                .get_parameter_slot_offset(slot)
                .map(|offset_start| {
                    codegen_inc_or_dec_expression_from_local_offset(
                        ty,
                        allocator,
                        ret,
                        offset_start,
                        IncDecExpression::PostIncrement,
                    )
                })
                .expect("local parameter stack slot is undeclared"),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    codegen_expr(allocator, ret, *expr),
                    codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret,
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
                ret,
                &identifier,
                IncDecExpression::PostDecrement,
            ),
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Local(slot)),
            ) => allocator
                .get_local_slot_offset(slot)
                .map(|offset_start| {
                    codegen_inc_or_dec_expression_from_local_offset(
                        ty,
                        allocator,
                        ret,
                        offset_start,
                        IncDecExpression::PostDecrement,
                    )
                })
                .expect("local stack slot is undeclared"),
            TypedExprNode::Primary(
                ty,
                Primary::Identifier(_, ast::IdentifierLocality::Parameter(slot)),
            ) => allocator
                .get_parameter_slot_offset(slot)
                .map(|offset_start| {
                    codegen_inc_or_dec_expression_from_local_offset(
                        ty,
                        allocator,
                        ret,
                        offset_start,
                        IncDecExpression::PostDecrement,
                    )
                })
                .expect("local paramater stack slot is undeclared"),
            TypedExprNode::Deref(ty, expr) => {
                flattenable_instructions!(
                    codegen_expr(allocator, ret, *expr),
                    codegen_inc_or_dec_expression_from_pointer(
                        ty,
                        allocator,
                        ret,
                        IncDecExpression::PostDecrement,
                    ),
                )
            }
            _ => unreachable!(),
        },

        TypedExprNode::Ref(_, ast::IdentifierLocality::Global(identifier)) => {
            codegen_reference_from_identifier(ret, &identifier)
        }
        TypedExprNode::Ref(_, ast::IdentifierLocality::Local(slot)) => allocator
            .get_local_slot_offset(slot)
            .map(|offset_start| codegen_reference_from_stack_offset(ret, offset_start))
            .expect("local stack slot is undeclared"),
        TypedExprNode::Ref(_, ast::IdentifierLocality::Parameter(slot)) => allocator
            .get_parameter_slot_offset(slot)
            .map(|offset_start| codegen_reference_from_stack_offset(ret, offset_start))
            .expect("local parameter stack slot is undeclared"),
        TypedExprNode::Deref(ty, expr) => {
            flattenable_instructions!(
                codegen_expr(allocator, ret, *expr),
                codegen_deref(ty, ret, 0),
            )
        }
        TypedExprNode::ScaleBy(ty, lhs) => {
            let scale_by_size = ty.size();
            codegen_scaleby(allocator, ret, scale_by_size, lhs)
        }
        TypedExprNode::Grouping(_, expr) => codegen_expr(allocator, ret, *expr),
    }
}

fn codegen_constant_i8<OP: Operand>(ret: &mut OP, constant: i8) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;
    vec![format!(
        "\tmov{}\t${}, {}\n",
        operator_suffix(WIDTH),
        constant,
        ret.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_u8<OP: Operand>(ret: &mut OP, constant: u8) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;
    vec![format!(
        "\tmov{}\t${}, {}\n",
        operator_suffix(WIDTH),
        constant,
        ret.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_i16<OP: Operand>(ret: &mut OP, constant: i16) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, {}\n",
        operator_suffix(WIDTH),
        constant,
        ret.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_u16<OP: Operand>(ret: &mut OP, constant: u16) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, {}\n",
        operator_suffix(WIDTH),
        constant,
        ret.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_i32<OP: Operand>(ret: &mut OP, constant: i32) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, {}\n",
        operator_suffix(WIDTH),
        constant,
        ret.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_u32<OP: Operand>(ret: &mut OP, constant: u32) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, {}\n",
        operator_suffix(WIDTH),
        constant,
        ret.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_i64<OP: Operand>(ret: &mut OP, constant: i64) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, {}\n",
        operator_suffix(WIDTH),
        constant,
        ret.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_constant_u64<OP: Operand>(ret: &mut OP, constant: u64) -> Vec<String> {
    const WIDTH: OperandWidth = OperandWidth::QuadWord;

    vec![format!(
        "\tmov{}\t${}, {}\n",
        operator_suffix(WIDTH),
        constant,
        ret.fmt_with_operand_width(WIDTH)
    )]
}

fn codegen_mov<SRC, DST>(ty: ast::Type, src: &mut SRC, dst: &mut DST) -> Vec<String>
where
    SRC: Operand,
    DST: Operand,
{
    let width = operand_width_of_type(ty);

    codegen_mov_with_explicit_width(width, src, dst)
}

fn codegen_mov_with_explicit_width<SRC, DST>(
    width: OperandWidth,
    src: &mut SRC,
    dst: &mut DST,
) -> Vec<String>
where
    SRC: Operand,
    DST: Operand,
{
    vec![format!(
        "\tmov{}\t{}, {}\n",
        operator_suffix(width),
        src.fmt_with_operand_width(width),
        dst.fmt_with_operand_width(width)
    )]
}

fn codegen_reference_from_identifier<OP: Operand>(ret: &mut OP, identifier: &str) -> Vec<String> {
    vec![format!(
        "\tleaq\t{}({}), {}\n",
        identifier,
        PointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ret.fmt_with_operand_width(OperandWidth::QuadWord)
    )]
}

fn codegen_reference_from_stack_offset<OP: Operand>(ret: &mut OP, offset: isize) -> Vec<String> {
    vec![format!(
        "\tleaq\t{}({}), {}\n",
        offset,
        BasePointerRegister.fmt_with_operand_width(OperandWidth::QuadWord),
        ret.fmt_with_operand_width(OperandWidth::QuadWord)
    )]
}

fn codegen_store_deref<SRC, DST>(ty: ast::Type, dest: &mut DST, src: &mut SRC) -> Vec<String>
where
    SRC: Operand,
    DST: Operand,
{
    let width = operand_width_of_type(ty);

    vec![format!(
        "\tmov{}\t{}, ({})\n",
        operator_suffix(width),
        src.fmt_with_operand_width(width),
        dest.fmt_with_operand_width(OperandWidth::QuadWord)
    )]
}

fn codegen_deref(
    ty: ast::Type,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    scale: usize,
) -> Vec<String> {
    let scale_by = ty.size() * scale;
    let width = operand_width_of_type(ty);

    if scale == 0 {
        vec![format!(
            "\tmov{}\t({}), {}\n",
            operator_suffix(width),
            ret.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    } else {
        vec![format!(
            "\tmov{}\t{}({}), {}\n",
            operator_suffix(width),
            scale_by,
            ret.fmt_with_operand_width(OperandWidth::QuadWord),
            ret.fmt_with_operand_width(width)
        )]
    }
}

fn codegen_scaleby(
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
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
            ret,
            ast::Type::Integer(sign, ast::IntegerWidth::SixtyFour),
            Box::new(scale_by_expr),
            expr,
        )
    } else {
        panic!("invalid scale_by types")
    }
}

fn codegen_addition(
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    ty: ast::Type,
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
        allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
            let lhs_ctx = codegen_expr(allocator, lhs_ret, *lhs);
            let rhs_ctx = codegen_expr(allocator, rhs_ret, *rhs);

            vec![
                lhs_ctx,
                rhs_ctx,
                codegen_mov(ty, rhs_ret, ret),
                vec![format!(
                    "\tadd{}\t{}, {}\n",
                    operator_suffix(width),
                    lhs_ret.fmt_with_operand_width(width),
                    ret.fmt_with_operand_width(width)
                )],
            ]
            .into_iter()
            .flatten()
            .collect()
        })
    })
}

fn codegen_subtraction(
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    ty: ast::Type,
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
        allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
            let lhs_ctx = codegen_expr(allocator, lhs_ret, *lhs);
            let rhs_ctx = codegen_expr(allocator, rhs_ret, *rhs);

            flattenable_instructions!(
                lhs_ctx,
                rhs_ctx,
                codegen_mov(ty, lhs_ret, ret),
                vec![format!(
                    "\tsub{}\t{}, {}\n",
                    operator_suffix(width),
                    rhs_ret.fmt_with_operand_width(width),
                    ret.fmt_with_operand_width(width)
                )],
            )
        })
    })
}

fn codegen_multiplication(
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    ty: ast::Type,
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
        allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
            let lhs_ctx = codegen_expr(allocator, lhs_ret, *lhs);
            let rhs_ctx = codegen_expr(allocator, rhs_ret, *rhs);

            flattenable_instructions!(
                lhs_ctx,
                rhs_ctx,
                codegen_mov(ty, rhs_ret, ret),
                vec![format!(
                    "\timul{}\t{}, {}\n",
                    operator_suffix(width),
                    lhs_ret.fmt_with_operand_width(width),
                    ret.fmt_with_operand_width(width)
                )],
            )
        })
    })
}

#[derive(Clone, Copy, PartialEq)]
enum DivisionVariant {
    Division,
    Modulo,
}

fn codegen_division(
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    ty: ast::Type,
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
    sign: ast::Signed,
    division_variant: DivisionVariant,
) -> Vec<String> {
    use crate::stage::type_check::ast::Signed;

    let width = operand_width_of_type(ty);

    allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
        allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
            let lhs_ctx = codegen_expr(allocator, lhs_ret, *lhs);
            let rhs_ctx = codegen_expr(allocator, rhs_ret, *rhs);
            let operand_suffix = operator_suffix(width);

            flattenable_instructions!(
                lhs_ctx,
                rhs_ctx,
                vec![
                    format!(
                        "\tmov{}\t{}, {}\n",
                        operand_suffix,
                        lhs_ret.fmt_with_operand_width(width),
                        IntegerRegister::A.fmt_with_operand_width(width)
                    ),
                    match sign {
                        Signed::Signed => format!(
                            "\tcqo\n\tidiv{}\t{}\n",
                            operand_suffix,
                            rhs_ret.fmt_with_operand_width(width)
                        ),
                        Signed::Unsigned => {
                            let d_reg =
                                IntegerRegister::D.fmt_with_operand_width(OperandWidth::QuadWord);

                            format!(
                                "\txorq\t{}, {}\n\tdiv{}\t{}\n",
                                d_reg,
                                d_reg,
                                operand_suffix,
                                rhs_ret.fmt_with_operand_width(width)
                            )
                        }
                    },
                    match division_variant {
                        DivisionVariant::Division => format!(
                            "\tmov{}\t{}, {}\n",
                            operand_suffix,
                            IntegerRegister::A.fmt_with_operand_width(width),
                            ret.fmt_with_operand_width(width)
                        ),
                        DivisionVariant::Modulo => format!(
                            "\tmov{}\t{}, {}\n",
                            operand_suffix,
                            IntegerRegister::D.fmt_with_operand_width(width),
                            ret.fmt_with_operand_width(width)
                        ),
                    }
                ],
            )
        })
    })
}

// Binary

fn codegen_or(
    ty: ast::Type,
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    lhs: ast::TypedExprNode,
    rhs: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
        allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
            let rhs_ctx = codegen_expr(allocator, rhs_ret, rhs);
            let lhs_ctx = codegen_expr(allocator, lhs_ret, lhs);

            flattenable_instructions!(
                rhs_ctx,
                lhs_ctx,
                codegen_mov(ty, lhs_ret, ret),
                vec![format!(
                    "\tor{}\t{}, {}\n",
                    operator_suffix(width),
                    rhs_ret.fmt_with_operand_width(width),
                    ret.fmt_with_operand_width(width)
                )],
            )
        })
    })
}

fn codegen_xor(
    ty: ast::Type,
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    lhs: ast::TypedExprNode,
    rhs: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
        allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
            let rhs_ctx = codegen_expr(allocator, rhs_ret, rhs);
            let lhs_ctx = codegen_expr(allocator, lhs_ret, lhs);

            flattenable_instructions!(
                rhs_ctx,
                lhs_ctx,
                codegen_mov(ty, lhs_ret, ret),
                vec![format!(
                    "\txor{}\t{}, {}\n",
                    operator_suffix(width),
                    rhs_ret.fmt_with_operand_width(width),
                    ret.fmt_with_operand_width(width)
                )],
            )
        })
    })
}

fn codegen_and(
    ty: ast::Type,
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    lhs: ast::TypedExprNode,
    rhs: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
        allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
            let rhs_ctx = codegen_expr(allocator, rhs_ret, rhs);
            let lhs_ctx = codegen_expr(allocator, lhs_ret, lhs);

            flattenable_instructions!(
                rhs_ctx,
                lhs_ctx,
                codegen_mov(ty, lhs_ret, ret),
                vec![format!(
                    "\tand{}\t{}, {}\n",
                    operator_suffix(width),
                    rhs_ret.fmt_with_operand_width(width),
                    ret.fmt_with_operand_width(width)
                )],
            )
        })
    })
}

fn codegen_shift_left(
    ty: ast::Type,
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    lhs: ast::TypedExprNode,
    rhs: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
        allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
            let rhs_ctx = codegen_expr(allocator, rhs_ret, rhs);
            let lhs_ctx = codegen_expr(allocator, lhs_ret, lhs);

            flattenable_instructions!(
                rhs_ctx,
                lhs_ctx,
                codegen_mov(ty, lhs_ret, ret),
                vec![
                    format!(
                        "\tmov{}\t{}, %cl\n",
                        operator_suffix(OperandWidth::Byte),
                        rhs_ret.fmt_with_operand_width(OperandWidth::Byte),
                    ),
                    format!(
                        "\tshl{}\t%cl, {}\n",
                        operator_suffix(width),
                        ret.fmt_with_operand_width(width)
                    )
                ],
            )
        })
    })
}

fn codegen_shift_right(
    ty: ast::Type,
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    lhs: ast::TypedExprNode,
    rhs: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
        allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
            let rhs_ctx = codegen_expr(allocator, rhs_ret, rhs);
            let lhs_ctx = codegen_expr(allocator, lhs_ret, lhs);

            flattenable_instructions!(
                rhs_ctx,
                lhs_ctx,
                codegen_mov(ty, lhs_ret, ret),
                vec![
                    format!(
                        "\tmov{}\t{}, %cl\n",
                        operator_suffix(OperandWidth::Byte),
                        rhs_ret.fmt_with_operand_width(OperandWidth::Byte),
                    ),
                    format!(
                        "\tshr{}\t%cl, {}\n",
                        operator_suffix(width),
                        ret.fmt_with_operand_width(width)
                    )
                ],
            )
        })
    })
}

/// Invert a register's value.
fn codegen_invert(
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    expr: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(expr.r#type());

    allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
        let ty = expr.r#type();
        let expr_ctx = codegen_expr(allocator, lhs_ret, expr);

        flattenable_instructions!(
            expr_ctx,
            codegen_mov(ty, lhs_ret, ret),
            vec![format!(
                "\tnot{}\t{}\n",
                operator_suffix(width),
                ret.fmt_with_operand_width(width)
            )],
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
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    comparison_op: ComparisonOperation,
    ty: ast::Type,
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
) -> Vec<String> {
    let width = operand_width_of_type(ty.clone());

    allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
        allocator.allocate_general_purpose_register_then(|allocator, rhs_ret| {
            let lhs_ctx = codegen_expr(allocator, lhs_ret, *lhs);
            let rhs_ctx = codegen_expr(allocator, rhs_ret, *rhs);

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
                codegen_mov(ty, rhs_ret, ret),
                vec![
                    format!(
                        "\tcmp{}\t{}, {}\n",
                        operand_suffix,
                        ret.fmt_with_operand_width(width),
                        lhs_ret.fmt_with_operand_width(width)
                    ),
                    format!(
                        "\t{}\t{}\n",
                        set_operator,
                        ret.fmt_with_operand_width(OperandWidth::Byte)
                    ),
                    format!(
                        "\tandq\t$255, {}\n",
                        ret.fmt_with_operand_width(OperandWidth::QuadWord)
                    ),
                ],
            )
        })
    })
}

fn codegen_compare_and_jmp<L>(
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    cond_true_id: L,
    cond_false_id: L,
) -> Vec<String>
where
    L: LabelFormattable,
{
    const WIDTH: OperandWidth = OperandWidth::QuadWord;
    let operand_suffix = operator_suffix(WIDTH);

    allocator.allocate_general_purpose_register_then(|_, zero_val| {
        vec![
            format!("\tandq\t$0, {}\n", zero_val.fmt_with_operand_width(WIDTH)),
            format!(
                "\tcmp{}\t{}, {}\n",
                operand_suffix,
                ret.fmt_with_operand_width(WIDTH),
                zero_val.fmt_with_operand_width(WIDTH)
            ),
            format!(
                "\t{}\t{}\n",
                "sete",
                ret.fmt_with_operand_width(OperandWidth::Byte)
            ),
            format!(
                "\tandq\t$255, {}\n",
                ret.fmt_with_operand_width(OperandWidth::QuadWord)
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
fn codegen_negate(
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    expr: ast::TypedExprNode,
) -> Vec<String> {
    let width = operand_width_of_type(expr.r#type());

    allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
        let ty = expr.r#type();
        let expr_ctx = codegen_expr(allocator, lhs_ret, expr);

        flattenable_instructions!(
            expr_ctx,
            codegen_mov(ty, lhs_ret, ret),
            vec![format!(
                "\tneg{}\t{}\n",
                operator_suffix(width),
                ret.fmt_with_operand_width(width)
            )],
        )
    })
}

/// Logically negate a register's value.
fn codegen_not(
    allocator: &mut SysVAllocator,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    expr: ast::TypedExprNode,
) -> Vec<String> {
    allocator.allocate_general_purpose_register_then(|allocator, lhs_ret| {
        let ty = expr.r#type();
        let expr_ctx = codegen_expr(allocator, lhs_ret, expr);
        let byte_ret_reg = ret.fmt_with_operand_width(OperandWidth::Byte);
        let quadword_ret_reg = ret.fmt_with_operand_width(OperandWidth::QuadWord);

        flattenable_instructions!(
            expr_ctx,
            codegen_mov(ty, lhs_ret, ret),
            vec![
                format!(
                    "\ttestq\t{width_adj_reg}, {width_adj_reg}\n",
                    width_adj_reg = quadword_ret_reg
                ),
                format!("\tsete\t{}\n", byte_ret_reg),
                format!("\tmovzbq\t{}, {}\n", byte_ret_reg, quadword_ret_reg)
            ],
        )
    })
}

fn codegen_call(
    allocator: &mut SysVAllocator,
    ty: ast::Type,
    ret: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    func_name: &str,
    arg: Option<Box<ast::TypedExprNode>>,
) -> Vec<String> {
    if let Some(arg_expr) = arg {
        let arg_expr_ty = arg_expr.r#type();

        allocator.allocate_general_purpose_register_then(|allocator, arg_ret| {
            let arg_ctx = codegen_expr(allocator, arg_ret, *arg_expr);

            flattenable_instructions!(
                arg_ctx,
                codegen_mov(arg_expr_ty.clone(), arg_ret, &mut IntegerRegister::D),
                vec![format!("\tcall\t{}\n", func_name)],
                codegen_mov(ty, &mut IntegerRegister::A, ret),
            )
        })
    } else {
        flattenable_instructions!(
            vec![format!("\tcall\t{}\n", func_name)],
            codegen_mov(ty, &mut IntegerRegister::A, ret),
        )
    }
}

fn codegen_return(
    ty: ast::Type,
    value_to_return: &mut RegisterOrOffset<&GeneralPurposeRegister>,
    func_name: &str,
) -> Vec<String> {
    flattenable_instructions!(
        codegen_mov(ty, value_to_return, &mut IntegerRegister::A),
        codegen_jump(format!("func_{}_ret", func_name)),
    )
}

const fn operator_suffix(width: OperandWidth) -> &'static str {
    match width {
        OperandWidth::QuadWord => "q",
        OperandWidth::DoubleWord => "l",
        OperandWidth::Word => "w",
        OperandWidth::Byte => "b",
    }
}

fn operand_width_of_type(ty: ast::Type) -> OperandWidth {
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

    macro_rules! compound_statements {
        ($($stmt:expr,)*) => {
               ast::TypedCompoundStmts::new(
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
                "\tmovq\t$10, %r14
\tmovq\t$3, %r13
\tmovb\t%r14b, %al
\txorq\t%rdx, %rdx
\tdivb\t%r13b
\tmovb\t%dl, %r15b
"
                .to_string(),
                "\tmovq\t$10, %r11
\tmovq\t$3, %r10
\tmovb\t%r11b, %al
\txorq\t%rdx, %rdx
\tdivb\t%r10b
\tmovb\t%al, %r12b
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
            Ok(vec!["\tleaq\tx(%rip), %r13
\tmovq\t$1, %r11
\tmovq\t$1, %r12
\tmovq\t%r12, %r14
\timulq\t%r11, %r14
\tmovq\t%r14, %r15
\taddq\t%r13, %r15
\tmovb\t(%r15), %r15b
"
            .to_string()]),
            X86_64.apply(compound_statements!(index_expression,))
        );
    }
}
