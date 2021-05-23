use crate::codegen::machine::arch::TargetArchitecture;
use crate::codegen::register::Register;
use crate::{ast::ExprNode, codegen::CodeGenerationErr};

/// X86_64 represents the x86_64 bit machine target.
pub struct X86_64;

mod register;
use register::{GPRegister, GPRegisterAllocator};

impl TargetArchitecture for X86_64 {}

#[derive(Default, Debug, Clone)]
pub struct SymbolTable {
    globals: std::collections::HashSet<String>,
}

impl SymbolTable {
    pub fn declare_global(&mut self, identifier: &str) {
        self.globals.insert(identifier.to_string());
    }

    pub fn assign_global(&mut self, identifier: &str) -> Option<()> {
        if self.globals.contains(identifier) {
            Some(())
        } else {
            None
        }
    }
}

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
        match input {
            ast::StmtNode::Expression(expr) => allocator.allocate_then(|allocator, ret_val| {
                Ok(vec![
                    codegen_expr(allocator, ret_val, expr),
                    codegen_printint(ret_val),
                ])
            }),
            ast::StmtNode::Declaration(identifier) => {
                symboltable.declare_global(&identifier);
                Ok(vec![codegen_global_symbol(&identifier)])
            }
            ast::StmtNode::Assignment(identifier, expr) => symboltable
                .assign_global(&identifier)
                .map(|_| {
                    allocator.allocate_then(|allocator, ret_val| {
                        vec![
                            codegen_expr(allocator, ret_val, expr),
                            codegen_store_global(ret_val, &identifier),
                        ]
                    })
                })
                .ok_or(CodeGenerationErr::UndefinedReference(identifier)),
        }
        .map(|insts| insts.into_iter().flatten().collect())
    }
}

pub fn codegen_preamble() -> Vec<String> {
    vec![String::from(machine::arch::x86_64::CG_PREAMBLE)]
}

pub fn codegen_postamble() -> Vec<String> {
    vec![String::from(machine::arch::x86_64::CG_POSTAMBLE)]
}

fn codegen_global_symbol(identifier: &str) -> Vec<String> {
    vec![format!("\t.comm\t{},1,8\n", identifier)]
}

fn codegen_store_global(ret: &mut GPRegister, identifier: &str) -> Vec<String> {
    vec![format!(
        "\tmov{}\t%{}, {}(%rip)\n",
        ret.operator_suffix(),
        ret.id(),
        identifier
    )]
}

fn codegen_load_global(ret: &mut GPRegister, identifier: &str) -> Vec<String> {
    vec![format!(
        "\tmov{}\t{}(%rip), %{}\n",
        ret.operator_suffix(),
        identifier,
        ret.id()
    )]
}

fn codegen_expr(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut GPRegister,
    expr: crate::ast::ExprNode,
) -> Vec<String> {
    use crate::ast::Primary;

    match expr {
        ExprNode::Primary(Primary::Uint8(ast::Uint8(uc))) => codegen_constant_u8(ret_val, uc),
        ExprNode::Primary(Primary::Identifier(identifier)) => {
            codegen_load_global(ret_val, &identifier)
        }

        ExprNode::Equal(lhs, rhs) => {
            codegen_compare(allocator, ret_val, ComparisonOperation::Equal, lhs, rhs)
        }
        ExprNode::NotEqual(lhs, rhs) => {
            codegen_compare(allocator, ret_val, ComparisonOperation::NotEqual, lhs, rhs)
        }
        ExprNode::LessThan(lhs, rhs) => {
            codegen_compare(allocator, ret_val, ComparisonOperation::LessThan, lhs, rhs)
        }
        ExprNode::GreaterThan(lhs, rhs) => codegen_compare(
            allocator,
            ret_val,
            ComparisonOperation::GreaterThan,
            lhs,
            rhs,
        ),
        ExprNode::LessEqual(lhs, rhs) => {
            codegen_compare(allocator, ret_val, ComparisonOperation::LessEqual, lhs, rhs)
        }
        ExprNode::GreaterEqual(lhs, rhs) => codegen_compare(
            allocator,
            ret_val,
            ComparisonOperation::GreaterEqual,
            lhs,
            rhs,
        ),

        ExprNode::Addition(lhs, rhs) => codegen_addition(allocator, ret_val, lhs, rhs),
        ExprNode::Subtraction(lhs, rhs) => codegen_subtraction(allocator, ret_val, lhs, rhs),
        ExprNode::Multiplication(lhs, rhs) => codegen_multiplication(allocator, ret_val, lhs, rhs),
        ExprNode::Division(lhs, rhs) => codegen_division(allocator, ret_val, lhs, rhs),
    }
}

fn codegen_constant_u8(ret_val: &mut GPRegister, constant: u8) -> Vec<String> {
    vec![format!(
        "\tmov{}\t${}, {}\n",
        ret_val.operator_suffix(),
        constant,
        ret_val
    )]
}

fn codegen_addition(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut GPRegister,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
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
    ret_val: &mut GPRegister,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> Vec<String> {
    allocator.allocate_then(|allocator, rhs_retval| {
        let lhs_ctx = codegen_expr(allocator, ret_val, *lhs);
        let rhs_ctx = codegen_expr(allocator, rhs_retval, *rhs);

        vec![
            lhs_ctx,
            rhs_ctx,
            vec![format!(
                "\tsub{}\t{}, {}\n",
                ret_val.operator_suffix(),
                ret_val,
                rhs_retval
            )],
        ]
        .into_iter()
        .flatten()
        .collect()
    })
}

fn codegen_multiplication(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut GPRegister,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> Vec<String> {
    allocator.allocate_then(|allocator, lhs_retval| {
        let lhs_ctx = codegen_expr(allocator, lhs_retval, *lhs);
        let rhs_ctx = codegen_expr(allocator, ret_val, *rhs);

        vec![
            lhs_ctx,
            rhs_ctx,
            vec![format!(
                "\timul{}\t{}, {}\n",
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

fn codegen_division(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut GPRegister,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> Vec<String> {
    allocator.allocate_then(|allocator, rhs_retval| {
        let lhs_ctx = codegen_expr(allocator, ret_val, *lhs);
        let rhs_ctx = codegen_expr(allocator, rhs_retval, *rhs);
        let operand_suffix = ret_val.operator_suffix();
        vec![
            lhs_ctx,
            rhs_ctx,
            vec![
                format!("\tmov{}\t{},%rax\n", operand_suffix, ret_val),
                String::from("\tcqo\n"),
                format!("\tidiv{}\t{}\n", operand_suffix, rhs_retval),
                format!("\tmov{}\t%rax,{}\n", operand_suffix, ret_val),
            ],
        ]
        .into_iter()
        .flatten()
        .collect()
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
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut GPRegister,
    comparison_op: ComparisonOperation,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
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

        vec![
            lhs_ctx,
            rhs_ctx,
            vec![
                format!("\tcmp{}\t{}, {}\n", operand_suffix, ret_val, lhs_retval),
                format!(
                    "\t{}\t{}\n",
                    set_operator,
                    GPRegister::new(ret_val.id(), register::GPRegisterMask::Byte)
                ),
                format!("\tandq\t$255,{}\n", ret_val),
            ],
        ]
        .into_iter()
        .flatten()
        .collect()
    })
}

fn codegen_printint(reg: &mut GPRegister) -> Vec<String> {
    vec![format!(
        "\tmov{}\t{}, %rdi\n\tcall\tprintint\n",
        reg.operator_suffix(),
        reg
    )]
}
