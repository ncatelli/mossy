use crate::ast;

mod register_allocation;

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

pub trait CodeGenerator {
    fn generate(self, input: ast::StmtNode) -> Result<Vec<String>, CodeGenerationErr>;
}

pub struct TargetCodeGenerator<T>
where
    T: crate::machine::arch::TargetArchitecture
        + crate::codegen::register_allocation::RegisterAllocatable,
{
    target_architecture: std::marker::PhantomData<T>,
    register_allocator: crate::codegen::register_allocation::RegisterAllocator<T>,
    context: Vec<String>,
}

impl<T> TargetCodeGenerator<T>
where
    T: crate::machine::arch::TargetArchitecture
        + crate::codegen::register_allocation::RegisterAllocatable,
{
    pub fn new() -> Self {
        Self {
            target_architecture: std::marker::PhantomData,
            register_allocator: crate::codegen::register_allocation::RegisterAllocator::new(),
            context: Vec::new(),
        }
    }
}

use crate::machine::arch;

impl CodeGenerator for TargetCodeGenerator<arch::X86_64> {
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

const X86_64CodeGenPreamble: &'static str = "\t.text
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

const X86_64CodeGenPostamble: &'static str = "\tmovl	$0, %eax
    popq	%rbp
    ret\n";

impl TargetCodeGenerator<arch::X86_64> {
    fn codegen_preamble(&mut self) {
        self.context.push(String::from(X86_64CodeGenPreamble));
    }

    fn codegen_postamble(&mut self) {
        self.context.push(String::from(X86_64CodeGenPostamble));
    }

    fn codegen_printint(&mut self, reg_id: RegisterId) {
        let reg = self.register_allocator.register(reg_id).unwrap();

        self.context
            .push(format!("\tmovq\t{}, %rdi\n\tcall\tprintint\n", reg));
        self.register_allocator.free_mut(reg_id);
    }

    fn codegen_expr(&mut self, expr: ast::ExprNode) -> RegisterId {
        use ast::{ExprNode, Primary};

        match expr {
            ExprNode::Primary(Primary::Uint8(ast::Uint8(ic))) => {
                let reg_id = self.register_allocator.allocate_mut().unwrap();
                let reg = self.register_allocator.register(reg_id).unwrap();
                self.context.push(format!("\tmovq\t${}, {}\n", ic, reg));
                reg_id
            }

            ExprNode::Addition(lhs, rhs) => {
                let r1_id = self.codegen_expr(*lhs);
                let r2_id = self.codegen_expr(*rhs);
                let r1 = self.register_allocator.register(r1_id).unwrap();
                let r2 = self.register_allocator.register(r2_id).unwrap();

                self.context.push(format!("\taddq\t{}, {}\n", r1, r2));
                self.register_allocator.free_mut(r1_id);
                r2_id
            }

            ExprNode::Subtraction(lhs, rhs) => {
                let r1_id = self.codegen_expr(*lhs);
                let r2_id = self.codegen_expr(*rhs);
                let r1 = self.register_allocator.register(r1_id).unwrap();
                let r2 = self.register_allocator.register(r2_id).unwrap();

                self.context.push(format!("\tsubq\t{}, {}\n", r2, r1));
                self.register_allocator.free_mut(r2_id);
                r1_id
            }

            ExprNode::Multiplication(lhs, rhs) => {
                let r1_id = self.codegen_expr(*lhs);
                let r2_id = self.codegen_expr(*rhs);
                let r1 = self.register_allocator.register(r1_id).unwrap();
                let r2 = self.register_allocator.register(r2_id).unwrap();

                self.context.push(format!("\timulq\t{}, {}\n", r1, r2));
                self.register_allocator.free_mut(r1_id);
                r2_id
            }

            ExprNode::Division(lhs, rhs) => {
                let r1_id = self.codegen_expr(*lhs);
                let r2_id = self.codegen_expr(*rhs);
                let r1 = self.register_allocator.register(r1_id).unwrap();
                let r2 = self.register_allocator.register(r2_id).unwrap();

                self.context.push(format!("\tmovq\t{},%%rax\n", r1));
                self.context.push(String::from("\tcqo\n"));
                self.context.push(format!("\tidivq\t{}\n", r2));
                self.context.push(format!("\tmovq\t%%rax,{}\n", r1));
                self.register_allocator.free_mut(r2_id);
                r1_id
            }
        }
    }
}
