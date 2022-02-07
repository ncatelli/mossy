use std::sync::mpsc;

pub trait WidthFormatted
where
    Self::Output: std::fmt::Display,
{
    type Output;
    fn fmt_with_operand_width(&self, width: OperandWidth) -> Self::Output;
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
    type Output = &'static str;

    fn fmt_with_operand_width(&self, width: OperandWidth) -> Self::Output {
        match width {
            OperandWidth::QuadWord => "%rip",
            OperandWidth::DoubleWord => "%eip",
            OperandWidth::Word => "%ip",
            OperandWidth::Byte => panic!("instruction pointer cannot be byte formatted"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BasePointerRegister;

impl WidthFormatted for BasePointerRegister {
    type Output = &'static str;

    fn fmt_with_operand_width(&self, width: OperandWidth) -> Self::Output {
        match width {
            OperandWidth::QuadWord => "%rbp",
            OperandWidth::DoubleWord => "%ebp",
            OperandWidth::Word => "%bp",
            OperandWidth::Byte => panic!("base pointer pointer cannot be byte formatted"),
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntegerRegister {
    A,
    B,
    C,
    D,
    SI,
    DI,
    BP,
    SP,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

impl WidthFormatted for IntegerRegister {
    type Output = &'static str;

    fn fmt_with_operand_width(&self, width: OperandWidth) -> Self::Output {
        match (self, width) {
            (IntegerRegister::A, OperandWidth::QuadWord) => "%rax",
            (IntegerRegister::A, OperandWidth::DoubleWord) => "%eax",
            (IntegerRegister::A, OperandWidth::Word) => "%ax",
            (IntegerRegister::A, OperandWidth::Byte) => "%al",
            (IntegerRegister::B, OperandWidth::QuadWord) => "%rbx",
            (IntegerRegister::B, OperandWidth::DoubleWord) => "%ebx",
            (IntegerRegister::B, OperandWidth::Word) => "%bx",
            (IntegerRegister::B, OperandWidth::Byte) => "%bl",
            (IntegerRegister::C, OperandWidth::QuadWord) => "%rcx",
            (IntegerRegister::C, OperandWidth::DoubleWord) => "%ecx",
            (IntegerRegister::C, OperandWidth::Word) => "%cx",
            (IntegerRegister::C, OperandWidth::Byte) => "%cl",
            (IntegerRegister::D, OperandWidth::QuadWord) => "%rdx",
            (IntegerRegister::D, OperandWidth::DoubleWord) => "%edx",
            (IntegerRegister::D, OperandWidth::Word) => "%dx",
            (IntegerRegister::D, OperandWidth::Byte) => "%dl",

            (IntegerRegister::SI, OperandWidth::QuadWord) => "%rsi",
            (IntegerRegister::SI, OperandWidth::DoubleWord) => "%esi",
            (IntegerRegister::SI, OperandWidth::Word) => "%si",
            (IntegerRegister::SI, OperandWidth::Byte) => "%sil",
            (IntegerRegister::DI, OperandWidth::QuadWord) => "%rdi",
            (IntegerRegister::DI, OperandWidth::DoubleWord) => "%edi",
            (IntegerRegister::DI, OperandWidth::Word) => "%di",
            (IntegerRegister::DI, OperandWidth::Byte) => "%dil",
            (IntegerRegister::BP, OperandWidth::QuadWord) => "%rbp",
            (IntegerRegister::BP, OperandWidth::DoubleWord) => "%ebp",
            (IntegerRegister::BP, OperandWidth::Word) => "%bp",
            (IntegerRegister::BP, OperandWidth::Byte) => "%bpl",
            (IntegerRegister::SP, OperandWidth::QuadWord) => "%rsp",
            (IntegerRegister::SP, OperandWidth::DoubleWord) => "%esp",
            (IntegerRegister::SP, OperandWidth::Word) => "%sp",
            (IntegerRegister::SP, OperandWidth::Byte) => "%spl",
            (IntegerRegister::R8, OperandWidth::QuadWord) => "%r8",
            (IntegerRegister::R8, OperandWidth::DoubleWord) => "%r8d",
            (IntegerRegister::R8, OperandWidth::Word) => "%r8w",
            (IntegerRegister::R8, OperandWidth::Byte) => "%r8b",
            (IntegerRegister::R9, OperandWidth::QuadWord) => "%r9",
            (IntegerRegister::R9, OperandWidth::DoubleWord) => "%r9d",
            (IntegerRegister::R9, OperandWidth::Word) => "%r9w",
            (IntegerRegister::R9, OperandWidth::Byte) => "%r9b",
            (IntegerRegister::R10, OperandWidth::QuadWord) => "%r10",
            (IntegerRegister::R10, OperandWidth::DoubleWord) => "%r10d",
            (IntegerRegister::R10, OperandWidth::Word) => "%r10w",
            (IntegerRegister::R10, OperandWidth::Byte) => "%r10b",
            (IntegerRegister::R11, OperandWidth::QuadWord) => "%r11",
            (IntegerRegister::R11, OperandWidth::DoubleWord) => "%r11d",
            (IntegerRegister::R11, OperandWidth::Word) => "%r11w",
            (IntegerRegister::R11, OperandWidth::Byte) => "%r11b",
            (IntegerRegister::R12, OperandWidth::QuadWord) => "%r12",
            (IntegerRegister::R12, OperandWidth::DoubleWord) => "%r12d",
            (IntegerRegister::R12, OperandWidth::Word) => "%r12w",
            (IntegerRegister::R12, OperandWidth::Byte) => "%r12b",
            (IntegerRegister::R13, OperandWidth::QuadWord) => "%r13",
            (IntegerRegister::R13, OperandWidth::DoubleWord) => "%r13d",
            (IntegerRegister::R13, OperandWidth::Word) => "%r13w",
            (IntegerRegister::R13, OperandWidth::Byte) => "%r13b",
            (IntegerRegister::R14, OperandWidth::QuadWord) => "%r14",
            (IntegerRegister::R14, OperandWidth::DoubleWord) => "%r14d",
            (IntegerRegister::R14, OperandWidth::Word) => "%r14w",
            (IntegerRegister::R14, OperandWidth::Byte) => "%r14b",
            (IntegerRegister::R15, OperandWidth::QuadWord) => "%r15",
            (IntegerRegister::R15, OperandWidth::DoubleWord) => "%r15d",
            (IntegerRegister::R15, OperandWidth::Word) => "%r15w",
            (IntegerRegister::R15, OperandWidth::Byte) => "%r15b",
        }
    }
}

impl From<GeneralPurposeRegister> for IntegerRegister {
    fn from(gpr: GeneralPurposeRegister) -> Self {
        match gpr {
            GeneralPurposeRegister::A => Self::A,
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
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
    A,
}

impl WidthFormatted for GeneralPurposeRegister {
    type Output = &'static str;

    fn fmt_with_operand_width(&self, width: OperandWidth) -> Self::Output {
        IntegerRegister::from(*self).fmt_with_operand_width(width)
    }
}

impl WidthFormatted for &GeneralPurposeRegister {
    type Output = &'static str;

    fn fmt_with_operand_width(&self, width: OperandWidth) -> Self::Output {
        IntegerRegister::from(**self).fmt_with_operand_width(width)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[allow(unused)]
pub enum FunctionPassingRegisters {
    DI,
    SI,
    D,
    C,
    R8,
    R9,
}

impl WidthFormatted for FunctionPassingRegisters {
    type Output = &'static str;

    fn fmt_with_operand_width(&self, width: OperandWidth) -> Self::Output {
        match self {
            FunctionPassingRegisters::DI => IntegerRegister::DI,
            FunctionPassingRegisters::SI => IntegerRegister::SI,
            FunctionPassingRegisters::D => IntegerRegister::D,
            FunctionPassingRegisters::C => IntegerRegister::C,
            FunctionPassingRegisters::R8 => IntegerRegister::R8,
            FunctionPassingRegisters::R9 => IntegerRegister::R9,
        }
        .fmt_with_operand_width(width)
    }
}

impl WidthFormatted for &FunctionPassingRegisters {
    type Output = &'static str;

    fn fmt_with_operand_width(&self, width: OperandWidth) -> Self::Output {
        (**self).fmt_with_operand_width(width)
    }
}

#[derive(Debug)]
pub(crate) struct RegisterAllocationGuard {
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

    pub(crate) fn borrow_inner(&self) -> &GeneralPurposeRegister {
        &self.reg
    }
}

impl WidthFormatted for RegisterAllocationGuard {
    type Output = &'static str;

    fn fmt_with_operand_width(&self, width: OperandWidth) -> Self::Output {
        self.reg.fmt_with_operand_width(width)
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

    pub(crate) fn allocate(&mut self) -> Option<RegisterAllocationGuard> {
        let reg = self.available.try_recv().ok()?;

        Some(RegisterAllocationGuard::new(self.freed.clone(), reg))
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
            GeneralPurposeRegister::A,
        ])
    }
}

#[cfg(test)]
mod tests {
    use crate::stage::codegen::machine::arch::x86_64;

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
