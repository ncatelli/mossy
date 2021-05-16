use crate::codegen::machine::arch::TargetArchitecture;
use crate::codegen::register::GeneralPurpose;
use crate::{ast::ExprNode, codegen::allocator::Allocator};

/// X86_64 represents the x86_64 bit machine target.
pub struct X86_64;

impl TargetArchitecture for X86_64 {}

#[derive(Debug, Clone)]
pub struct GPRegisterAllocator {
    general_purpose: [GeneralPurpose<u64>; 8],
    general_purpose_allocated: [bool; 8],
}

impl Default for GPRegisterAllocator {
    fn default() -> Self {
        Self {
            general_purpose: [
                GeneralPurpose::new("%r8"),
                GeneralPurpose::new("%r9"),
                GeneralPurpose::new("%r10"),
                GeneralPurpose::new("%r11"),
                GeneralPurpose::new("%r12"),
                GeneralPurpose::new("%r13"),
                GeneralPurpose::new("%r14"),
                GeneralPurpose::new("%r15"),
            ],
            general_purpose_allocated: [false, false, false, false, false, false, false, false],
        }
    }
}

impl GPRegisterAllocator {
    /// Optionally returns a register, by Id, if it exists.
    pub fn register(&self, idx: usize) -> Option<GeneralPurpose<u64>> {
        self.general_purpose.get(idx).copied()
    }

    pub fn register_ids(&self) -> Vec<&'static str> {
        self.general_purpose.iter().map(|reg| reg.id()).collect()
    }
}

impl Allocator for GPRegisterAllocator {
    /// Finds the first unallocated register, if one is found it is returned
    /// as an option.
    fn allocate_mut(&mut self) -> Option<usize> {
        if let Some(idx) = get_unallocated_register(self) {
            self.general_purpose_allocated[idx] = true;
            Some(idx)
        } else {
            None
        }
    }

    /// Finds the first unallocated register, if one is found it is returned
    /// as an option.
    fn allocate(mut self) -> (Self, Option<usize>) {
        let allocated_id = self.allocate_mut();
        (self, allocated_id)
    }

    fn free_mut(&mut self, idx: usize) -> Option<usize> {
        if let Some(alloc) = self.general_purpose_allocated.get_mut(idx) {
            *alloc = false;
            Some(idx)
        } else {
            None
        }
    }

    fn free(mut self, idx: usize) -> (Self, Option<usize>) {
        let idx = self.free_mut(idx);
        (self, idx)
    }

    fn free_all_mut(&mut self) {
        self.general_purpose_allocated = [false, false, false, false, false, false, false, false]
    }

    fn free_all(mut self) -> Self {
        self.free_all_mut();
        self
    }
}

/// Finds the first unallocated register, if any, If any are available the offset is returned.
fn get_unallocated_register(ra: &GPRegisterAllocator) -> Option<usize> {
    ra.general_purpose_allocated
        .iter()
        .enumerate()
        .filter_map(|(idx, allocated)| if *allocated { None } else { Some(idx) })
        .next()
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

type RegisterId = usize;

impl CodeGenerator
    for codegen::TargetCodeGenerator<
        machine::arch::x86_64::X86_64,
        machine::arch::x86_64::GPRegisterAllocator,
    >
{
    fn generate(mut self, input: ast::StmtNode) -> Result<Vec<String>, codegen::CodeGenerationErr> {
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

impl
    codegen::TargetCodeGenerator<
        machine::arch::x86_64::X86_64,
        machine::arch::x86_64::GPRegisterAllocator,
    >
{
    fn codegen_preamble(&mut self) {
        self.context
            .push(String::from(machine::arch::x86_64::CG_PREAMBLE));
    }

    fn codegen_postamble(&mut self) {
        self.context
            .push(String::from(machine::arch::x86_64::CG_POSTAMBLE));
    }

    fn codegen_printint(&mut self, reg_id: RegisterId) {
        let reg = self.allocator.register(reg_id).unwrap();

        self.context
            .push(format!("\tmovq\t{}, %rdi\n\tcall\tprintint\n", reg));
        self.allocator.free_mut(reg_id);
    }

    fn codegen_expr(&mut self, expr: crate::ast::ExprNode) -> RegisterId {
        use crate::ast::Primary;

        match expr {
            ExprNode::Primary(Primary::Uint8(ast::Uint8(uc))) => self.codegen_constant_u8(uc),
            ExprNode::Addition(lhs, rhs) => self.codegen_addition(lhs, rhs),
            ExprNode::Subtraction(lhs, rhs) => self.codegen_subtraction(lhs, rhs),
            ExprNode::Multiplication(lhs, rhs) => self.codegen_multiplication(lhs, rhs),
            ExprNode::Division(lhs, rhs) => self.codegen_division(lhs, rhs),
        }
    }
}

impl
    codegen::TargetCodeGenerator<
        machine::arch::x86_64::X86_64,
        machine::arch::x86_64::GPRegisterAllocator,
    >
{
    fn codegen_constant_u8(&mut self, constant: u8) -> RegisterId {
        let reg_id = self.allocator.allocate_mut().unwrap();
        let reg = self.allocator.register(reg_id).unwrap();
        self.context
            .push(format!("\tmovq\t${}, {}\n", constant, reg));
        reg_id
    }

    fn codegen_addition(&mut self, lhs: Box<ExprNode>, rhs: Box<ExprNode>) -> RegisterId {
        let r1_id = self.codegen_expr(*lhs);
        let r2_id = self.codegen_expr(*rhs);
        let r1 = self.allocator.register(r1_id).unwrap();
        let r2 = self.allocator.register(r2_id).unwrap();

        self.context.push(format!("\taddq\t{}, {}\n", r1, r2));
        self.allocator.free_mut(r1_id);
        r2_id
    }

    fn codegen_subtraction(&mut self, lhs: Box<ExprNode>, rhs: Box<ExprNode>) -> RegisterId {
        let r1_id = self.codegen_expr(*lhs);
        let r2_id = self.codegen_expr(*rhs);
        let r1 = self.allocator.register(r1_id).unwrap();
        let r2 = self.allocator.register(r2_id).unwrap();

        self.context.push(format!("\tsubq\t{}, {}\n", r2, r1));
        self.allocator.free_mut(r2_id);
        r1_id
    }

    fn codegen_multiplication(&mut self, lhs: Box<ExprNode>, rhs: Box<ExprNode>) -> RegisterId {
        let r1_id = self.codegen_expr(*lhs);
        let r2_id = self.codegen_expr(*rhs);
        let r1 = self.allocator.register(r1_id).unwrap();
        let r2 = self.allocator.register(r2_id).unwrap();

        self.context.push(format!("\timulq\t{}, {}\n", r1, r2));
        self.allocator.free_mut(r1_id);
        r2_id
    }

    fn codegen_division(&mut self, lhs: Box<ExprNode>, rhs: Box<ExprNode>) -> RegisterId {
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
