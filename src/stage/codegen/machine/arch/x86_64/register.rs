use crate::stage::codegen::register::{AddressWidth, Register};
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

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Registers {
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

impl WidthFormatted for Registers {
    fn fmt_with_operand_width(&self, width: OperandWidth) -> &'static str {
        match (self, width) {
            (Registers::A, OperandWidth::QuadWord) => "rax",
            (Registers::A, OperandWidth::DoubleWord) => "eax",
            (Registers::A, OperandWidth::Word) => "ax",
            (Registers::A, OperandWidth::Byte) => "al",
            (Registers::B, OperandWidth::QuadWord) => "rbx",
            (Registers::B, OperandWidth::DoubleWord) => "ebx",
            (Registers::B, OperandWidth::Word) => "bx",
            (Registers::B, OperandWidth::Byte) => "bl",
            (Registers::C, OperandWidth::QuadWord) => "rcx",
            (Registers::C, OperandWidth::DoubleWord) => "ecx",
            (Registers::C, OperandWidth::Word) => "cx",
            (Registers::C, OperandWidth::Byte) => "cl",
            (Registers::D, OperandWidth::QuadWord) => "rdx",
            (Registers::D, OperandWidth::DoubleWord) => "edx",
            (Registers::D, OperandWidth::Word) => "dx",
            (Registers::D, OperandWidth::Byte) => "dl",

            (Registers::SI, OperandWidth::QuadWord) => "rsi",
            (Registers::SI, OperandWidth::DoubleWord) => "esi",
            (Registers::SI, OperandWidth::Word) => "si",
            (Registers::SI, OperandWidth::Byte) => "sil",
            (Registers::DI, OperandWidth::QuadWord) => "rdi",
            (Registers::DI, OperandWidth::DoubleWord) => "edi",
            (Registers::DI, OperandWidth::Word) => "di",
            (Registers::DI, OperandWidth::Byte) => "dil",
            (Registers::BP, OperandWidth::QuadWord) => "rbp",
            (Registers::BP, OperandWidth::DoubleWord) => "ebp",
            (Registers::BP, OperandWidth::Word) => "bp",
            (Registers::BP, OperandWidth::Byte) => "bpl",
            (Registers::R8, OperandWidth::QuadWord) => "r8",
            (Registers::R8, OperandWidth::DoubleWord) => "r8d",
            (Registers::R8, OperandWidth::Word) => "r8w",
            (Registers::R8, OperandWidth::Byte) => "r8b",
            (Registers::R9, OperandWidth::QuadWord) => "r9",
            (Registers::R9, OperandWidth::DoubleWord) => "r9d",
            (Registers::R9, OperandWidth::Word) => "r9w",
            (Registers::R9, OperandWidth::Byte) => "r9b",
            (Registers::R10, OperandWidth::QuadWord) => "r10",
            (Registers::R10, OperandWidth::DoubleWord) => "r10d",
            (Registers::R10, OperandWidth::Word) => "r10w",
            (Registers::R10, OperandWidth::Byte) => "r10b",
            (Registers::R11, OperandWidth::QuadWord) => "r11",
            (Registers::R11, OperandWidth::DoubleWord) => "r11d",
            (Registers::R11, OperandWidth::Word) => "r11w",
            (Registers::R11, OperandWidth::Byte) => "r11b",
            (Registers::R12, OperandWidth::QuadWord) => "r12",
            (Registers::R12, OperandWidth::DoubleWord) => "r12d",
            (Registers::R12, OperandWidth::Word) => "r12w",
            (Registers::R12, OperandWidth::Byte) => "r12b",
            (Registers::R13, OperandWidth::QuadWord) => "r13",
            (Registers::R13, OperandWidth::DoubleWord) => "r13d",
            (Registers::R13, OperandWidth::Word) => "r13w",
            (Registers::R13, OperandWidth::Byte) => "r13b",
            (Registers::R14, OperandWidth::QuadWord) => "r14",
            (Registers::R14, OperandWidth::DoubleWord) => "r14d",
            (Registers::R14, OperandWidth::Word) => "r14w",
            (Registers::R14, OperandWidth::Byte) => "r14b",
            (Registers::R15, OperandWidth::QuadWord) => "r15",
            (Registers::R15, OperandWidth::DoubleWord) => "r15d",
            (Registers::R15, OperandWidth::Word) => "r15w",
            (Registers::R15, OperandWidth::Byte) => "r15b",
        }
    }
}

impl From<GeneralPurposeRegisters> for Registers {
    fn from(gpr: GeneralPurposeRegisters) -> Self {
        match gpr {
            GeneralPurposeRegisters::R8 => Self::R8,
            GeneralPurposeRegisters::R9 => Self::R9,
            GeneralPurposeRegisters::R10 => Self::R10,
            GeneralPurposeRegisters::R11 => Self::R11,
            GeneralPurposeRegisters::R12 => Self::R12,
            GeneralPurposeRegisters::R13 => Self::R13,
            GeneralPurposeRegisters::R14 => Self::R14,
            GeneralPurposeRegisters::R15 => Self::R15,
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneralPurposeRegisters {
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

impl WidthFormatted for GeneralPurposeRegisters {
    fn fmt_with_operand_width(&self, width: OperandWidth) -> &'static str {
        Registers::from(*self).fmt_with_operand_width(width)
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
pub enum SizedGeneralPurpose {
    QuadWord(&'static str),
    DoubleWord(&'static str),
    Word(&'static str),
    Byte(&'static str),
}

impl AddressWidth for SizedGeneralPurpose {
    fn bits(&self) -> usize {
        match self {
            SizedGeneralPurpose::QuadWord(_) => 64,
            SizedGeneralPurpose::DoubleWord(_) => 32,
            SizedGeneralPurpose::Word(_) => 16,
            SizedGeneralPurpose::Byte(_) => 8,
        }
    }
}

impl Register<u64> for SizedGeneralPurpose {
    /// returns the string representation of the register.
    fn id(&self) -> &'static str {
        match self {
            SizedGeneralPurpose::QuadWord(id) => id,
            SizedGeneralPurpose::DoubleWord(id) => id,
            SizedGeneralPurpose::Word(id) => id,
            SizedGeneralPurpose::Byte(id) => id,
        }
    }
}

impl SizedGeneralPurpose {
    pub fn resize(mut self, width: OperandWidth) -> Self {
        self.resize_mut(width);
        self
    }

    pub fn resize_mut(&mut self, width: OperandWidth) {
        let id = self.id();
        *self = match width {
            OperandWidth::QuadWord => SizedGeneralPurpose::QuadWord(id),
            OperandWidth::DoubleWord => SizedGeneralPurpose::DoubleWord(id),
            OperandWidth::Word => SizedGeneralPurpose::Word(id),
            OperandWidth::Byte => SizedGeneralPurpose::Byte(id),
        };
    }

    pub fn operator_suffix(&self) -> &'static str {
        match self {
            SizedGeneralPurpose::QuadWord(_) => "q",
            SizedGeneralPurpose::DoubleWord(_) => "l",
            SizedGeneralPurpose::Word(_) => "w",
            SizedGeneralPurpose::Byte(_) => "b",
        }
    }
}

impl core::fmt::Display for SizedGeneralPurpose {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let repr = self.id();
        let register_suffix = match self {
            SizedGeneralPurpose::QuadWord(_) => "",
            SizedGeneralPurpose::DoubleWord(_) => "d",
            SizedGeneralPurpose::Word(_) => "w",
            SizedGeneralPurpose::Byte(_) => "b",
        };

        write!(f, "%{}{}", repr, register_suffix)
    }
}

#[derive(Debug)]
struct RegisterAllocationGuard {
    free_channel: std::sync::mpsc::Sender<SizedGeneralPurpose>,
    reg: SizedGeneralPurpose,
}

impl RegisterAllocationGuard {
    fn new(
        free_channel: std::sync::mpsc::Sender<SizedGeneralPurpose>,
        reg: SizedGeneralPurpose,
    ) -> Self {
        Self { free_channel, reg }
    }

    #[allow(dead_code)]
    fn borrow_inner(&self) -> &SizedGeneralPurpose {
        &self.reg
    }

    fn borrow_inner_mut(&mut self) -> &mut SizedGeneralPurpose {
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
    freed: mpsc::Sender<SizedGeneralPurpose>,
    available: mpsc::Receiver<SizedGeneralPurpose>,
}

impl GPRegisterAllocator {
    #[allow(dead_code)]
    pub fn new(registers: Vec<SizedGeneralPurpose>) -> Self {
        let (freed, available_registers) = mpsc::channel();

        for register in registers {
            freed.send(register).expect("cannot seed channel.");
        }

        Self {
            freed,
            available: available_registers,
        }
    }

    fn allocate_with_width(&mut self, width: OperandWidth) -> Option<RegisterAllocationGuard> {
        let reg = self.available.try_recv().ok()?.resize(width);

        Some(RegisterAllocationGuard::new(self.freed.clone(), reg))
    }

    /// Allocates a register for the duration of the life of closure.
    pub fn allocate_then<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self, &mut SizedGeneralPurpose) -> R,
    {
        self.allocate_with_width_then(OperandWidth::QuadWord, f)
    }

    /// Allocates a register for the duration of the life of closure with a given width.
    pub fn allocate_with_width_then<F, R>(&mut self, width: OperandWidth, f: F) -> R
    where
        F: FnOnce(&mut Self, &mut SizedGeneralPurpose) -> R,
    {
        self.allocate_with_width(width)
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
            SizedGeneralPurpose::QuadWord("r15"),
            SizedGeneralPurpose::QuadWord("r14"),
            SizedGeneralPurpose::QuadWord("r13"),
            SizedGeneralPurpose::QuadWord("r12"),
            SizedGeneralPurpose::QuadWord("r11"),
            SizedGeneralPurpose::QuadWord("r10"),
            SizedGeneralPurpose::QuadWord("r9"),
            SizedGeneralPurpose::QuadWord("r8"),
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stage::codegen::machine::arch::x86_64;
    use crate::stage::codegen::register::Register;

    #[test]
    fn should_allocate_a_register_from_an_unutilized_pool() {
        assert_eq!(
            ["r14", "r15"],
            x86_64::GPRegisterAllocator::default().allocate_then(|allocator, reg| {
                [allocator.allocate_then(|_, reg| reg.id()), reg.id()]
            })
        )
    }

    #[test]
    fn should_free_allocations_on_scope_exit() {
        let mut allocator = x86_64::GPRegisterAllocator::default();
        let mut guards = Vec::new();

        for _ in 0..9 {
            guards.push(allocator.allocate_with_width(OperandWidth::QuadWord));
        }

        // pool should be empty
        assert!(allocator
            .allocate_with_width(OperandWidth::QuadWord)
            .is_none());

        // should free up register leases.
        drop(guards);
        assert!(allocator
            .allocate_with_width(OperandWidth::QuadWord)
            .is_some());
    }
}
