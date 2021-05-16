use crate::ast;

pub mod allocator;
pub mod machine;
mod register;

use allocator::Allocator;

/// CodeGenerationErr represents an error stemming from the CodeGenerator's
/// `generate` method, capturing any potential point of breakdown withing the
/// code generation process.
#[derive(Clone, PartialEq)]
pub enum CodeGenerationErr {
    Unspecified(String),
}

impl std::fmt::Debug for CodeGenerationErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CodeGenerationErr::Unspecified(e) => {
                write!(f, "unspecified code generation err: {}", e)
            }
        }
    }
}

/// CodeGenerator defines the generate method, returning a string representation
/// of all generated instructions or an error.
pub trait CodeGenerator {
    fn generate(self, input: ast::StmtNode) -> Result<Vec<String>, CodeGenerationErr>;
}

/// TargetCodeGenerator implmements CodeGenerator, storing code context,
/// register allocator and other metadata for a specific architecture.
pub struct TargetCodeGenerator<T, A>
where
    T: machine::arch::TargetArchitecture,
    A: allocator::Allocator<register::GeneralPurpose<u64>>,
{
    target_architecture: std::marker::PhantomData<T>,
    allocator: A,
    context: Vec<String>,
}

impl<T, R> TargetCodeGenerator<T, R>
where
    T: machine::arch::TargetArchitecture,
    R: allocator::Allocator<register::GeneralPurpose<u64>> + Default,
{
    pub fn new() -> Self {
        Self::default()
    }
}

impl<T, R> Default for TargetCodeGenerator<T, R>
where
    T: machine::arch::TargetArchitecture,
    R: allocator::Allocator<register::GeneralPurpose<u64>> + Default,
{
    fn default() -> Self {
        Self {
            target_architecture: std::marker::PhantomData,
            allocator: <R>::default(),
            context: Vec::new(),
        }
    }
}

impl CodeGenerator
    for TargetCodeGenerator<
        machine::arch::x86_64::X86_64,
        machine::arch::x86_64::GPRegisterAllocator,
    >
{
    fn generate(mut self, input: ast::StmtNode) -> Result<Vec<String>, CodeGenerationErr> {
        self.codegen_preamble();
        match input {
            ast::StmtNode::Expression(expr) => {
                let reg_id = self.codegen_expr(expr);
                self.codegen_printint(reg_id);
            }
        };

        self.codegen_postamble();
        Ok(self.context)
    }
}

type RegisterId = usize;

const X86_64_PREAMBLE: &str = "\t.text
.LC0:
    .string\t\"%d\\n\"
printint:
    pushq\t%rbp
    movq\t%rsp, %rbp
    subq\t$16, %rsp
    movl\t%edi, -4(%rbp)
    movl\t-4(%rbp), %eax
    movl\t%eax, %esi
    leaq	.LC0(%rip), %rdi
    movl	$0, %eax
    call	printf@PLT
    nop
    leave
    ret
	
    .globl\tmain
    .type\tmain, @function
main:
    pushq\t%rbp
    movq	%rsp, %rbp\n";

const X86_64_POSTAMBLE: &str = "\tmovl	$0, %eax
    popq	%rbp
    ret\n";

impl
    TargetCodeGenerator<machine::arch::x86_64::X86_64, machine::arch::x86_64::GPRegisterAllocator>
{
    fn codegen_preamble(&mut self) {
        self.context.push(String::from(X86_64_PREAMBLE));
    }

    fn codegen_postamble(&mut self) {
        self.context.push(String::from(X86_64_POSTAMBLE));
    }

    fn codegen_printint(&mut self, reg_id: RegisterId) {
        let reg = self.allocator.register(reg_id).unwrap();

        self.context
            .push(format!("\tmovq\t{}, %rdi\n\tcall\tprintint\n", reg));
        self.allocator.free_mut(reg_id);
    }

    fn codegen_expr(&mut self, expr: ast::ExprNode) -> RegisterId {
        use ast::{ExprNode, Primary};

        match expr {
            ExprNode::Primary(Primary::Uint8(ast::Uint8(ic))) => {
                let reg_id = self.allocator.allocate_mut().unwrap();
                let reg = self.allocator.register(reg_id).unwrap();
                self.context.push(format!("\tmovq\t${}, {}\n", ic, reg));
                reg_id
            }

            ExprNode::Addition(lhs, rhs) => {
                let r1_id = self.codegen_expr(*lhs);
                let r2_id = self.codegen_expr(*rhs);
                let r1 = self.allocator.register(r1_id).unwrap();
                let r2 = self.allocator.register(r2_id).unwrap();

                self.context.push(format!("\taddq\t{}, {}\n", r1, r2));
                self.allocator.free_mut(r1_id);
                r2_id
            }

            ExprNode::Subtraction(lhs, rhs) => {
                let r1_id = self.codegen_expr(*lhs);
                let r2_id = self.codegen_expr(*rhs);
                let r1 = self.allocator.register(r1_id).unwrap();
                let r2 = self.allocator.register(r2_id).unwrap();

                self.context.push(format!("\tsubq\t{}, {}\n", r2, r1));
                self.allocator.free_mut(r2_id);
                r1_id
            }

            ExprNode::Multiplication(lhs, rhs) => {
                let r1_id = self.codegen_expr(*lhs);
                let r2_id = self.codegen_expr(*rhs);
                let r1 = self.allocator.register(r1_id).unwrap();
                let r2 = self.allocator.register(r2_id).unwrap();

                self.context.push(format!("\timulq\t{}, {}\n", r1, r2));
                self.allocator.free_mut(r1_id);
                r2_id
            }

            ExprNode::Division(lhs, rhs) => {
                let r1_id = self.codegen_expr(*lhs);
                let r2_id = self.codegen_expr(*rhs);
                let r1 = self.allocator.register(r1_id).unwrap();
                let r2 = self.allocator.register(r2_id).unwrap();

                self.context.push(format!("\tmovq\t{},%%rax\n", r1));
                self.context.push(String::from("\tcqo\n"));
                self.context.push(format!("\tidivq\t{}\n", r2));
                self.context.push(format!("\tmovq\t%%rax,{}\n", r1));
                self.allocator.free_mut(r2_id);
                r1_id
            }
        }
    }
}
