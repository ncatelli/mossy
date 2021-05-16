use crate::codegen::allocator::Allocator;
use crate::codegen::machine::arch::TargetArchitecture;
use crate::codegen::register::GeneralPurpose;

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

impl Allocator<GeneralPurpose<u64>> for GPRegisterAllocator {
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
