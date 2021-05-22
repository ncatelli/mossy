use crate::codegen::machine::arch::TargetArchitecture;
use crate::{ast::ExprNode, codegen::CodeGenerationErr};

/// X86_64 represents the x86_64 bit machine target.
pub struct X86_64;

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

#[derive(Debug, Clone, Copy)]
pub enum SizedGeneralPurpose {
    QuadWord(&'static str),
    DoubleWord(&'static str),
    Word(&'static str),
    Byte(&'static str),
}

impl SizedGeneralPurpose {
    /// returns the string representation of the register.
    fn id(&self) -> &'static str {
        match self {
            SizedGeneralPurpose::QuadWord(id) => id,
            SizedGeneralPurpose::DoubleWord(id) => id,
            SizedGeneralPurpose::Word(id) => id,
            SizedGeneralPurpose::Byte(id) => id,
        }
    }

    fn operand_suffix(&self) -> &'static str {
        match self {
            SizedGeneralPurpose::QuadWord(_) => "q",
            SizedGeneralPurpose::DoubleWord(_) => "l",
            SizedGeneralPurpose::Word(_) => "w",
            SizedGeneralPurpose::Byte(_) => "b",
        }
    }
}

impl std::fmt::Display for SizedGeneralPurpose {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let repr = self.id();

        write!(f, "%{}", repr,)
    }
}

#[derive(Debug, Clone)]
pub struct GPRegisterAllocator {
    registers: Vec<SizedGeneralPurpose>,
}

impl GPRegisterAllocator {
    pub fn new(registers: Vec<SizedGeneralPurpose>) -> Self {
        Self { registers }
    }

    /// Allocates a register for the duration of the life of closure.
    fn allocate_then<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self, &mut SizedGeneralPurpose) -> R,
    {
        self.registers
            .pop()
            .map(|mut reg| {
                let ret_val = f(self, &mut reg);
                self.registers.push(reg);
                ret_val
            })
            .unwrap()
    }
}

impl Default for GPRegisterAllocator {
    fn default() -> Self {
        Self {
            registers: vec![
                SizedGeneralPurpose::QuadWord("r8"),
                SizedGeneralPurpose::QuadWord("r9"),
                SizedGeneralPurpose::QuadWord("r10"),
                SizedGeneralPurpose::QuadWord("r11"),
                SizedGeneralPurpose::QuadWord("r12"),
                SizedGeneralPurpose::QuadWord("r13"),
                SizedGeneralPurpose::QuadWord("r14"),
                SizedGeneralPurpose::QuadWord("r15"),
            ],
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

fn codegen_store_global(ret: &mut SizedGeneralPurpose, identifier: &str) -> Vec<String> {
    vec![format!(
        "\tmov{}\t{}, {}(%rip)\n",
        ret.operand_suffix(),
        ret.id(),
        identifier
    )]
}

fn codegen_load_global(ret: &mut SizedGeneralPurpose, identifier: &str) -> Vec<String> {
    vec![format!(
        "\tmov{}\t{}(%rip), {}\n",
        ret.operand_suffix(),
        identifier,
        ret.id()
    )]
}

fn codegen_expr(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
    expr: crate::ast::ExprNode,
) -> Vec<String> {
    use crate::ast::Primary;

    match expr {
        ExprNode::Primary(Primary::Uint8(ast::Uint8(uc))) => codegen_constant_u8(ret_val, uc),
        ExprNode::Primary(Primary::Identifier(identifier)) => {
            codegen_load_global(ret_val, &identifier)
        }

        ExprNode::Equal(_, _) => vec![],
        ExprNode::NotEqual(_, _) => vec![],
        ExprNode::LessThan(_, _) => vec![],
        ExprNode::GreaterThan(_, _) => vec![],
        ExprNode::LessEqual(_, _) => vec![],
        ExprNode::GreaterEqual(_, _) => vec![],

        ExprNode::Addition(lhs, rhs) => codegen_addition(allocator, ret_val, lhs, rhs),
        ExprNode::Subtraction(lhs, rhs) => codegen_subtraction(allocator, ret_val, lhs, rhs),
        ExprNode::Multiplication(lhs, rhs) => codegen_multiplication(allocator, ret_val, lhs, rhs),
        ExprNode::Division(lhs, rhs) => codegen_division(allocator, ret_val, lhs, rhs),
    }
}

fn codegen_constant_u8(ret_val: &mut SizedGeneralPurpose, constant: u8) -> Vec<String> {
    vec![format!(
        "\tmov{}\t${}, {}\n",
        ret_val.operand_suffix(),
        constant,
        ret_val
    )]
}

fn codegen_addition(
    allocator: &mut GPRegisterAllocator,
    ret_val: &mut SizedGeneralPurpose,
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
                ret_val.operand_suffix(),
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
                ret_val.operand_suffix(),
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
    ret_val: &mut SizedGeneralPurpose,
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
                ret_val.operand_suffix(),
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
    ret_val: &mut SizedGeneralPurpose,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> Vec<String> {
    allocator.allocate_then(|allocator, rhs_retval| {
        let lhs_ctx = codegen_expr(allocator, ret_val, *lhs);
        let rhs_ctx = codegen_expr(allocator, rhs_retval, *rhs);
        let operand_suffix = ret_val.operand_suffix();
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

fn codegen_printint(reg: &mut SizedGeneralPurpose) -> Vec<String> {
    vec![format!(
        "\tmov{}\t{}, %rdi\n\tcall\tprintint\n",
        reg.operand_suffix(),
        reg
    )]
}

#[cfg(test)]
mod tests {
    use crate::codegen::machine::arch::x86_64;

    #[test]
    fn should_allocate_a_register_from_an_unutilized_pool() {
        assert_eq!(
            ["%r14", "%r15"],
            x86_64::GPRegisterAllocator::default().allocate_then(|allocator, reg| {
                [allocator.allocate_then(|_, reg| reg.id()), reg.id()]
            })
        )
    }

    #[test]
    fn should_free_allocations_on_scope_exit() {
        let mut allocator = x86_64::GPRegisterAllocator::default();
        let initial_len = allocator.registers.len();

        // allocator pool should decrease by 1 while allocated in scope.
        allocator
            .allocate_then(|allocator, _| assert_eq!(initial_len - 1, allocator.registers.len()));

        // register should be freed on scope exit.
        assert_eq!(initial_len, allocator.registers.len());
    }
}
