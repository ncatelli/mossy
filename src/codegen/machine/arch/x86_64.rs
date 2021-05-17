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

struct ReturningCodeGeneratorContext {
    insts: Vec<String>,
    ret_val: RegisterId,
}

impl ReturningCodeGeneratorContext {
    fn new(insts: Vec<String>, ret_val: RegisterId) -> Self {
        Self { insts, ret_val }
    }
}

struct NonReturningCodeGeneratorContext {
    insts: Vec<String>,
}

impl NonReturningCodeGeneratorContext {
    fn new(insts: Vec<String>) -> Self {
        Self { insts }
    }
}

impl CodeGenerator for X86_64 {
    fn generate(self, input: ast::StmtNode) -> Result<Vec<String>, codegen::CodeGenerationErr> {
        let mut allocator = GPRegisterAllocator::default();
        let inst = match input {
            ast::StmtNode::Expression(expr) => {
                let cg_ctx = codegen_expr(&mut allocator, expr);
                let print_inst = codegen_printint(&mut allocator, cg_ctx.ret_val);
                vec![cg_ctx.insts, print_inst.insts]
            }
        };

        let ctx = vec![
            codegen_preamble(),
            inst.into_iter().flatten().collect(),
            codegen_postamble(),
        ]
        .into_iter()
        .flatten()
        .collect();

        Ok(ctx)
    }
}

fn codegen_preamble() -> Vec<String> {
    vec![String::from(machine::arch::x86_64::CG_PREAMBLE)]
}

fn codegen_postamble() -> Vec<String> {
    vec![String::from(machine::arch::x86_64::CG_POSTAMBLE)]
}

fn codegen_expr(
    allocator: &mut GPRegisterAllocator,
    expr: crate::ast::ExprNode,
) -> ReturningCodeGeneratorContext {
    use crate::ast::Primary;

    match expr {
        ExprNode::Primary(Primary::Uint8(ast::Uint8(uc))) => codegen_constant_u8(allocator, uc),
        ExprNode::Addition(lhs, rhs) => codegen_addition(allocator, lhs, rhs),
        ExprNode::Subtraction(lhs, rhs) => codegen_subtraction(allocator, lhs, rhs),
        ExprNode::Multiplication(lhs, rhs) => codegen_multiplication(allocator, lhs, rhs),
        ExprNode::Division(lhs, rhs) => codegen_division(allocator, lhs, rhs),
    }
}

fn codegen_constant_u8(
    allocator: &mut GPRegisterAllocator,
    constant: u8,
) -> ReturningCodeGeneratorContext {
    let reg_id = allocator.allocate_mut().unwrap();
    let reg = allocator.register(reg_id).unwrap();
    ReturningCodeGeneratorContext::new(vec![format!("\tmovq\t${}, {}\n", constant, reg)], reg_id)
}

fn codegen_addition(
    allocator: &mut GPRegisterAllocator,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> ReturningCodeGeneratorContext {
    let lhs_ctx = codegen_expr(allocator, *lhs);
    let rhs_ctx = codegen_expr(allocator, *rhs);

    let r1 = allocator.register(lhs_ctx.ret_val).unwrap();
    let r2 = allocator.register(rhs_ctx.ret_val).unwrap();

    let generated = vec![
        lhs_ctx.insts,
        rhs_ctx.insts,
        vec![format!("\taddq\t{}, {}\n", r1, r2)],
    ]
    .into_iter()
    .flatten()
    .collect();

    allocator.free_mut(rhs_ctx.ret_val);
    ReturningCodeGeneratorContext::new(generated, rhs_ctx.ret_val)
}

fn codegen_subtraction(
    allocator: &mut GPRegisterAllocator,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> ReturningCodeGeneratorContext {
    let lhs_ctx = codegen_expr(allocator, *lhs);
    let rhs_ctx = codegen_expr(allocator, *rhs);
    let r1 = allocator.register(lhs_ctx.ret_val).unwrap();
    let r2 = allocator.register(rhs_ctx.ret_val).unwrap();

    let generated = vec![
        lhs_ctx.insts,
        rhs_ctx.insts,
        vec![format!("\tsubq\t{}, {}\n", r2, r1)],
    ]
    .into_iter()
    .flatten()
    .collect();

    allocator.free_mut(rhs_ctx.ret_val);
    ReturningCodeGeneratorContext::new(generated, lhs_ctx.ret_val)
}

fn codegen_multiplication(
    allocator: &mut GPRegisterAllocator,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> ReturningCodeGeneratorContext {
    let lhs_ctx = codegen_expr(allocator, *lhs);
    let rhs_ctx = codegen_expr(allocator, *rhs);
    let r1 = allocator.register(lhs_ctx.ret_val).unwrap();
    let r2 = allocator.register(rhs_ctx.ret_val).unwrap();

    let generated = vec![
        lhs_ctx.insts,
        rhs_ctx.insts,
        vec![format!("\timulq\t{}, {}\n", r1, r2)],
    ]
    .into_iter()
    .flatten()
    .collect();

    allocator.free_mut(lhs_ctx.ret_val);
    ReturningCodeGeneratorContext::new(generated, rhs_ctx.ret_val)
}

fn codegen_division(
    allocator: &mut GPRegisterAllocator,
    lhs: Box<ExprNode>,
    rhs: Box<ExprNode>,
) -> ReturningCodeGeneratorContext {
    let lhs_ctx = codegen_expr(allocator, *lhs);
    let rhs_ctx = codegen_expr(allocator, *rhs);
    let r1 = allocator.register(lhs_ctx.ret_val).unwrap();
    let r2 = allocator.register(rhs_ctx.ret_val).unwrap();

    let generated = vec![
        lhs_ctx.insts,
        rhs_ctx.insts,
        vec![
            format!("\tmovq\t{},%%rax\n", r1),
            String::from("\tcqo\n"),
            format!("\tidivq\t{}\n", r2),
            format!("\tmovq\t%%rax,{}\n", r1),
        ],
    ]
    .into_iter()
    .flatten()
    .collect();
    allocator.free_mut(rhs_ctx.ret_val);
    ReturningCodeGeneratorContext::new(generated, lhs_ctx.ret_val)
}

fn codegen_printint(
    allocator: &mut GPRegisterAllocator,
    reg_id: RegisterId,
) -> NonReturningCodeGeneratorContext {
    let reg = allocator.register(reg_id).unwrap();
    NonReturningCodeGeneratorContext::new(vec![format!(
        "\tmovq\t{}, %rdi\n\tcall\tprintint\n",
        reg
    )])
}
