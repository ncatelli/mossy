use std::sync::mpsc;

pub trait WidthFormatted {
    fn fmt_with_operand_width(&self, width: OperandWidth) -> &'static str;
}

/// Represents the width of an operand
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperandWidth {
    QuadWord,
    DoubleWord,
    Word,
    Byte,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PointerRegister;

impl WidthFormatted for PointerRegister {
    fn fmt_with_operand_width(&self, width: OperandWidth) -> &'static str {
        match width {
            OperandWidth::QuadWord => "rip",
            OperandWidth::DoubleWord => "eip",
            OperandWidth::Word => "ip",
            OperandWidth::Byte => panic!("instruction pointer cannot be byte formatted"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BasePointerRegister;

impl WidthFormatted for BasePointerRegister {
    fn fmt_with_operand_width(&self, width: OperandWidth) -> &'static str {
        match width {
            OperandWidth::QuadWord => "rbp",
            OperandWidth::DoubleWord => "ebp",
            OperandWidth::Word => "bp",
            OperandWidth::Byte => panic!("base pointer pointer cannot be byte formatted"),
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarRegister {
    A,
    B,
    C,
    D,
    SI,
    DI,
    BP,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

impl WidthFormatted for ScalarRegister {
    fn fmt_with_operand_width(&self, width: OperandWidth) -> &'static str {
        match (self, width) {
            (ScalarRegister::A, OperandWidth::QuadWord) => "rax",
            (ScalarRegister::A, OperandWidth::DoubleWord) => "eax",
            (ScalarRegister::A, OperandWidth::Word) => "ax",
            (ScalarRegister::A, OperandWidth::Byte) => "al",
            (ScalarRegister::B, OperandWidth::QuadWord) => "rbx",
            (ScalarRegister::B, OperandWidth::DoubleWord) => "ebx",
            (ScalarRegister::B, OperandWidth::Word) => "bx",
            (ScalarRegister::B, OperandWidth::Byte) => "bl",
            (ScalarRegister::C, OperandWidth::QuadWord) => "rcx",
            (ScalarRegister::C, OperandWidth::DoubleWord) => "ecx",
            (ScalarRegister::C, OperandWidth::Word) => "cx",
            (ScalarRegister::C, OperandWidth::Byte) => "cl",
            (ScalarRegister::D, OperandWidth::QuadWord) => "rdx",
            (ScalarRegister::D, OperandWidth::DoubleWord) => "edx",
            (ScalarRegister::D, OperandWidth::Word) => "dx",
            (ScalarRegister::D, OperandWidth::Byte) => "dl",

            (ScalarRegister::SI, OperandWidth::QuadWord) => "rsi",
            (ScalarRegister::SI, OperandWidth::DoubleWord) => "esi",
            (ScalarRegister::SI, OperandWidth::Word) => "si",
            (ScalarRegister::SI, OperandWidth::Byte) => "sil",
            (ScalarRegister::DI, OperandWidth::QuadWord) => "rdi",
            (ScalarRegister::DI, OperandWidth::DoubleWord) => "edi",
            (ScalarRegister::DI, OperandWidth::Word) => "di",
            (ScalarRegister::DI, OperandWidth::Byte) => "dil",
            (ScalarRegister::BP, OperandWidth::QuadWord) => "rbp",
            (ScalarRegister::BP, OperandWidth::DoubleWord) => "ebp",
            (ScalarRegister::BP, OperandWidth::Word) => "bp",
            (ScalarRegister::BP, OperandWidth::Byte) => "bpl",
            (ScalarRegister::R8, OperandWidth::QuadWord) => "r8",
            (ScalarRegister::R8, OperandWidth::DoubleWord) => "r8d",
            (ScalarRegister::R8, OperandWidth::Word) => "r8w",
            (ScalarRegister::R8, OperandWidth::Byte) => "r8b",
            (ScalarRegister::R9, OperandWidth::QuadWord) => "r9",
            (ScalarRegister::R9, OperandWidth::DoubleWord) => "r9d",
            (ScalarRegister::R9, OperandWidth::Word) => "r9w",
            (ScalarRegister::R9, OperandWidth::Byte) => "r9b",
            (ScalarRegister::R10, OperandWidth::QuadWord) => "r10",
            (ScalarRegister::R10, OperandWidth::DoubleWord) => "r10d",
            (ScalarRegister::R10, OperandWidth::Word) => "r10w",
            (ScalarRegister::R10, OperandWidth::Byte) => "r10b",
            (ScalarRegister::R11, OperandWidth::QuadWord) => "r11",
            (ScalarRegister::R11, OperandWidth::DoubleWord) => "r11d",
            (ScalarRegister::R11, OperandWidth::Word) => "r11w",
            (ScalarRegister::R11, OperandWidth::Byte) => "r11b",
            (ScalarRegister::R12, OperandWidth::QuadWord) => "r12",
            (ScalarRegister::R12, OperandWidth::DoubleWord) => "r12d",
            (ScalarRegister::R12, OperandWidth::Word) => "r12w",
            (ScalarRegister::R12, OperandWidth::Byte) => "r12b",
            (ScalarRegister::R13, OperandWidth::QuadWord) => "r13",
            (ScalarRegister::R13, OperandWidth::DoubleWord) => "r13d",
            (ScalarRegister::R13, OperandWidth::Word) => "r13w",
            (ScalarRegister::R13, OperandWidth::Byte) => "r13b",
            (ScalarRegister::R14, OperandWidth::QuadWord) => "r14",
            (ScalarRegister::R14, OperandWidth::DoubleWord) => "r14d",
            (ScalarRegister::R14, OperandWidth::Word) => "r14w",
            (ScalarRegister::R14, OperandWidth::Byte) => "r14b",
            (ScalarRegister::R15, OperandWidth::QuadWord) => "r15",
            (ScalarRegister::R15, OperandWidth::DoubleWord) => "r15d",
            (ScalarRegister::R15, OperandWidth::Word) => "r15w",
            (ScalarRegister::R15, OperandWidth::Byte) => "r15b",
        }
    }
}

impl From<GeneralPurposeRegister> for ScalarRegister {
    fn from(gpr: GeneralPurposeRegister) -> Self {
        match gpr {
            GeneralPurposeRegister::R8 => Self::R8,
            GeneralPurposeRegister::R9 => Self::R9,
            GeneralPurposeRegister::R10 => Self::R10,
            GeneralPurposeRegister::R11 => Self::R11,
            GeneralPurposeRegister::R12 => Self::R12,
            GeneralPurposeRegister::R13 => Self::R13,
            GeneralPurposeRegister::R14 => Self::R14,
            GeneralPurposeRegister::R15 => Self::R15,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneralPurposeRegister {
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

impl WidthFormatted for GeneralPurposeRegister {
    fn fmt_with_operand_width(&self, width: OperandWidth) -> &'static str {
        ScalarRegister::from(*self).fmt_with_operand_width(width)
    }
}

#[derive(Debug)]
struct RegisterAllocationGuard {
    free_channel: std::sync::mpsc::Sender<GeneralPurposeRegister>,
    reg: GeneralPurposeRegister,
}

impl RegisterAllocationGuard {
    fn new(
        free_channel: std::sync::mpsc::Sender<GeneralPurposeRegister>,
        reg: GeneralPurposeRegister,
    ) -> Self {
        Self { free_channel, reg }
    }

    #[allow(dead_code)]
    fn borrow_inner(&self) -> &GeneralPurposeRegister {
        &self.reg
    }

    fn borrow_inner_mut(&mut self) -> &mut GeneralPurposeRegister {
        &mut self.reg
    }
}

impl core::ops::Drop for RegisterAllocationGuard {
    fn drop(&mut self) {
        self.free_channel
            .send(self.reg)
            .expect("register allocation guard outlives allocator");
    }
}

#[derive(Debug)]
pub struct GPRegisterAllocator {
    freed: mpsc::Sender<GeneralPurposeRegister>,
    available: mpsc::Receiver<GeneralPurposeRegister>,
}

impl GPRegisterAllocator {
    #[allow(dead_code)]
    pub fn new(registers: Vec<GeneralPurposeRegister>) -> Self {
        let (freed, available_registers) = mpsc::channel();

        for register in registers {
            freed.send(register).expect("cannot seed channel.");
        }

        Self {
            freed,
            available: available_registers,
        }
    }

    fn allocate(&mut self) -> Option<RegisterAllocationGuard> {
        let reg = self.available.try_recv().ok()?;

        Some(RegisterAllocationGuard::new(self.freed.clone(), reg))
    }

    /// Allocates a register for the duration of the life of closure.
    pub fn allocate_then<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self, &mut GeneralPurposeRegister) -> R,
    {
        self.allocate()
            .map(|mut guard| {
                let ret_val = f(self, guard.borrow_inner_mut());
                ret_val
            })
            .expect("unable to allocate register")
    }
}

impl Default for GPRegisterAllocator {
    fn default() -> Self {
        Self::new(vec![
            GeneralPurposeRegister::R15,
            GeneralPurposeRegister::R14,
            GeneralPurposeRegister::R13,
            GeneralPurposeRegister::R12,
            GeneralPurposeRegister::R11,
            GeneralPurposeRegister::R10,
            GeneralPurposeRegister::R9,
            GeneralPurposeRegister::R8,
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stage::codegen::machine::arch::x86_64;

    #[test]
    fn should_allocate_a_register_from_an_unutilized_pool() {
        assert_eq!(
            ["r14", "r15"],
            x86_64::GPRegisterAllocator::default().allocate_then(|allocator, reg| {
                [
                    allocator
                        .allocate_then(|_, reg| reg.fmt_with_operand_width(OperandWidth::QuadWord)),
                    reg.fmt_with_operand_width(OperandWidth::QuadWord),
                ]
            })
        )
    }

    #[test]
    fn should_free_allocations_on_scope_exit() {
        let mut allocator = x86_64::GPRegisterAllocator::default();
        let mut guards = Vec::new();

        for _ in 0..9 {
            guards.push(allocator.allocate());
        }

        // pool should be empty
        assert!(allocator.allocate().is_none());

        // should free up register leases.
        drop(guards);
        assert!(allocator.allocate().is_some());
    }
}
