use crate::stage::ast::{self, ByteSized, Type};
use crate::stage::codegen::machine::arch::TargetArchitecture;
use crate::stage::codegen::{self, machine, register::Register, CodeGenerationErr};
use crate::stage::CompilationStage;
use core::sync::atomic::{AtomicUsize, Ordering};

static BLOCK_ID: AtomicUsize = AtomicUsize::new(0);

/// X86_64 represents the x86_64 bit machine target.
pub struct X86_64;

mod register;
use register::{GPRegisterAllocator, SizedGeneralPurpose};

impl TargetArchitecture for X86_64 {}

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

impl CompilationStage<ast::TypedProgram, Vec<String>, String> for X86_64 {
    fn apply(&mut self, input: ast::TypedProgram) -> Result<Vec<String>, String> {
        input
            .defs
            .into_iter()
            .map(|global_decl| {
                let mut allocator = GPRegisterAllocator::default();

                let res: Result<Vec<String>, CodeGenerationErr> = match global_decl {
                    ast::TypedGlobalDecls::Func(func) => {
                        let (id, block) = (func.id, func.block);

                        codegen_statements(&mut allocator, block)
                            .map(|block| {
                                vec![
                                    codegen_function_preamble(&id),
                                    block,
                                    codegen_function_postamble(&id),
                                ]
                            })
                            .map(|output| output.into_iter().flatten().collect())
                    }
                    ast::TypedGlobalDecls::Var(ast::Declaration(ty, identifiers)) => {
                        let globals = identifiers
                            .iter()
                            .map(|id| codegen_global_symbol(&ty, id))
                            .flatten()
                            .collect();
                        Ok(globals)
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
        let mut allocator = GPRegisterAllocator::default();
        let (id, block) = (input.id, input.block);

        codegen_statements(&mut allocator, block)
            .map(|block| {
                vec![
                    codegen_function_preamble(&id),
                    block,
                    codegen_function_postamble(&id),
                ]
            })
            .map(|output| output.into_iter().flatten().collect())
    }
}

impl CompilationStage<ast::TypedCompoundStmts, Vec<String>, CodeGenerationErr> for X86_64 {
    fn apply(&mut self, input: ast::TypedCompoundStmts) -> Result<Vec<String>, CodeGenerationErr> {
        let mut allocator = GPRegisterAllocator::default();
        codegen_statements(&mut allocator, input)
    }
}

fn codegen_statements(
    allocator: &mut GPRegisterAllocator,
    input: ast::TypedCompoundStmts,
) -> Result<Vec<String>, CodeGenerationErr> {
    let stmts = Vec::<ast::TypedStmtNode>::from(input);

    stmts
        .into_iter()
        .map(|stmt| codegen_statement(allocator, stmt).map(|output| output.join("")))
        .collect::<Result<Vec<String>, _>>()
}

fn codegen_statement(
    allocator: &mut GPRegisterAllocator,
    input: ast::TypedStmtNode,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    match input {
        ast::TypedStmtNode::Expression(expr) => allocator
            .allocate_then(|allocator, ret_val| Ok(vec![codegen_expr(allocator, ret_val, expr)])),
        ast::TypedStmtNode::Declaration(ast::Declaration(ty, identifiers)) => {
            let var_decls = identifiers
                .iter()
                .map(|id| codegen_global_symbol(&ty, id))
                .collect();
            Ok(var_decls)
        }
        ast::TypedStmtNode::Return(_, id, arg) => allocator.allocate_then(|allocator, ret_val| {
            let res: Vec<String> = if let Some(expr) = arg {
                codegen_expr(allocator, ret_val, expr)
            } else {
                vec![]
            }
            .into_iter()
            .chain(codegen_return(ret_val, &id))
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
    cond: ast::TypedExprNode,
    true_case: ast::TypedCompoundStmts,
    false_case: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_then(|allocator, ret_val| {
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let exit_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let true_case_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let tctx = codegen_statements(allocator, true_case)?;
        let else_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_ctx = codegen_statements(allocator, false_case)?;

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
    cond: ast::TypedExprNode,
    true_case: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_then(|allocator, ret_val| {
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let exit_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let true_case_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let tctx = codegen_statements(allocator, true_case)?;

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
    cond: ast::TypedExprNode,
    block: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_then(|allocator, ret_val| {
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let loop_cond_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_start_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_end_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_insts = codegen_statements(allocator, block)?;

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
    preop: ast::TypedStmtNode,
    cond: ast::TypedExprNode,
    postop: ast::TypedStmtNode,
    block: ast::TypedCompoundStmts,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    allocator.allocate_then(|allocator, ret_val| {
        let preop_ctx = codegen_statement(allocator, preop)?;
        let cond_ctx = codegen_expr(allocator, ret_val, cond);
        let postop_ctx = codegen_statement(allocator, postop)?;
        let loop_cond_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_start_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let loop_end_block_id = BLOCK_ID.fetch_add(1, Ordering::SeqCst);
        let block_insts = codegen_statements(allocator, block)?;

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

pub fn codegen_function_preamble(identifier: &str) -> Vec<String> {
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

pub fn codegen_function_postamble(identifier: &str) -> Vec<String> {
    codegen_label(format!("func_{}_ret", identifier))
        .into_iter()
        .chain(
            vec!["\tpopq     %rbp
    ret\n\n"
                .to_string()]
            .into_iter(),
        )
        .collect()
}

fn codegen_global_symbol(kind: &Type, identifier: &str) -> Vec<String> {
    const ALIGNMENT: usize = 2;
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

fn codegen_label<T>(block_id: T) -> Vec<String>
where
    T: core::fmt::Display,
{
    vec![format!("L{}:\n", block_id)]
}

fn codegen_jump<T>(block_id: T) -> Vec<String>
where
    T: core::fmt::Display,
{
    vec![format!("\tjmp\tL{}\n", block_id)]
}

fn codegen_expr(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    expr: ast::TypedExprNode,
) -> Vec<String> {
    use crate::stage::ast::{IntegerWidth, Primary, Signed, TypedExprNode};

    match expr {
        TypedExprNode::Primary(
            _,
            Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::SixtyFour,
                value,
            },
        ) => codegen_constant_u64(ret_val, value),
        TypedExprNode::Primary(
            _,
            Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::ThirtyTwo,
                value,
            },
        ) => {
            let uc = core::convert::TryFrom::try_from(value)
                .expect("value exceeds unsigned 32-bit integer");
            codegen_constant_u32(ret_val, uc)
        }
        TypedExprNode::Primary(
            _,
            Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::Sixteen,
                value,
            },
        ) => {
            let uc = core::convert::TryFrom::try_from(value)
                .expect("value exceeds unsigned 32-bit integer");
            codegen_constant_u16(ret_val, uc)
        }
        TypedExprNode::Primary(
            _,
            Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::Eight,
                value,
            },
        ) => {
            let uc = core::convert::TryFrom::try_from(value)
                .expect("value exceeds unsigned 8-bit integer");
            codegen_constant_u8(ret_val, uc)
        }
        TypedExprNode::Primary(
            _,
            Primary::Integer {
                sign: Signed::Signed,
                width: _,
                value: _,
            },
        ) => {
            todo!();
        }
        TypedExprNode::Primary(_, Primary::Identifier(_, identifier)) => {
            codegen_load_global(ret_val, &identifier)
        }

        TypedExprNode::FunctionCall(_, func_name, optional_arg) => {
            codegen_call(allocator, ret_val, &func_name, optional_arg)
        }

        ast::TypedExprNode::Assignment(_, identifier, expr) => {
            allocator.allocate_then(|allocator, ret_val| {
                flattenable_instructions!(
                    codegen_expr(allocator, ret_val, *expr),
                    codegen_store_global(ret_val, &identifier),
                )
            })
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

        TypedExprNode::Addition(Type::Pointer(_), lhs, rhs) => {
            codegen_addition(allocator, ret_val, lhs, rhs)
        }
        TypedExprNode::Addition(_, lhs, rhs) => codegen_addition(allocator, ret_val, lhs, rhs),
        TypedExprNode::Subtraction(_, lhs, rhs) => {
            codegen_subtraction(allocator, ret_val, lhs, rhs)
        }
        TypedExprNode::Multiplication(_, lhs, rhs) => {
            codegen_multiplication(allocator, ret_val, lhs, rhs)
        }
        TypedExprNode::Division(_, lhs, rhs) => codegen_division(allocator, ret_val, lhs, rhs),
        TypedExprNode::Ref(_, identifier) => codegen_reference(ret_val, &identifier),
        TypedExprNode::Deref(ty, expr) => {
            flattenable_instructions!(
                codegen_expr(allocator, ret_val, *expr),
                codegen_deref(ret_val, ty),
            )
        }
        TypedExprNode::ScaleBy(ty, lhs) => {
            let scale_by_size = ty.size();
            codegen_scaleby(allocator, ret_val, scale_by_size, lhs)
        }
    }
}

fn codegen_constant_u64(ret_val: &mut SizedGeneralPurpose, constant: u64) -> Vec<String> {
    vec![format!(
        "\tmov{}\t${}, {}\n",
        ret_val.operator_suffix(),
        constant,
        ret_val
    )]
}

fn codegen_constant_u32(ret_val: &mut SizedGeneralPurpose, constant: u32) -> Vec<String> {
    vec![format!(
        "\tmov{}\t${}, {}\n",
        ret_val.operator_suffix(),
        constant,
        ret_val
    )]
}

fn codegen_constant_u16(ret_val: &mut SizedGeneralPurpose, constant: u16) -> Vec<String> {
    vec![format!(
        "\tmov{}\t${}, {}\n",
        ret_val.operator_suffix(),
        constant,
        ret_val
    )]
}

fn codegen_constant_u8(ret_val: &mut SizedGeneralPurpose, constant: u8) -> Vec<String> {
    vec![format!(
        "\tmov{}\t${}, {}\n",
        ret_val.operator_suffix(),
        constant,
        ret_val
    )]
}

fn codegen_reference(ret: &mut SizedGeneralPurpose, identifier: &str) -> Vec<String> {
    vec![format!("\tleaq\t{}(%rip), %{}\n", identifier, ret.id())]
}

fn codegen_deref(ret: &mut SizedGeneralPurpose, _: ast::Type) -> Vec<String> {
    vec![format!(
        "\tmov{}\t(%{}), %{}\n",
        ret.operator_suffix(),
        ret.id(),
        ret.id()
    )]
}

fn codegen_scaleby(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    size_of: usize,
    expr: Box<ast::TypedExprNode>,
) -> Vec<String> {
    use ast::Typed;

    if let ast::Type::Integer(sign, width) = expr.r#type() {
        let scale_by_expr = ast::TypedExprNode::Primary(
            ast::Type::Integer(sign, width),
            ast::Primary::Integer {
                sign,
                width,
                value: size_of as u64,
            },
        );

        codegen_multiplication(allocator, ret_val, expr, Box::new(scale_by_expr))
    } else {
        panic!("invalid scale_by types")
    }
}

fn codegen_addition(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
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
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
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
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
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
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
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
    lhs: Box<ast::TypedExprNode>,
    rhs: Box<ast::TypedExprNode>,
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

fn codegen_call(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    func_name: &str,
    arg: Option<Box<ast::TypedExprNode>>,
) -> Vec<String> {
    if let Some(arg_expr) = arg {
        allocator.allocate_then(|allocator, arg_retval| {
            let arg_ctx = codegen_expr(allocator, arg_retval, *arg_expr);

            flattenable_instructions!(
                arg_ctx,
                vec![
                    format!(
                        "\tmov{}\t{}, %rdi\n",
                        arg_retval.operator_suffix(),
                        arg_retval,
                    ),
                    format!("\tcall\t{}\n", func_name),
                    format!("\tmov{}\t%rax, {}\n", ret_val.operator_suffix(), ret_val,),
                ],
            )
        })
    } else {
        vec![
            format!("\tcall\t{}\n", func_name),
            format!("\tmov{}\t%rax, {}\n", ret_val.operator_suffix(), ret_val,),
        ]
    }
}

fn codegen_return(ret_val: &mut SizedGeneralPurpose, func_name: &str) -> Vec<String> {
    vec![format!(
        "\tmov{}\t{}, %rax\n",
        ret_val.operator_suffix(),
        ret_val,
    )]
    .into_iter()
    .chain(codegen_jump(format!("func_{}_ret", func_name)).into_iter())
    .collect()
}

#[allow(dead_code)]
fn codegen_printint(reg: &mut SizedGeneralPurpose) -> Vec<String> {
    vec![format!(
        "\tmov{}\t{}, %rdi\n\tcall\tprintint\n",
        reg.operator_suffix(),
        reg
    )]
}
