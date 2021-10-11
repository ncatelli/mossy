use crate::codegen::register::{AddressWidth, Register};
use std::sync::mpsc;

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

impl crate::codegen::register::Register<u64> for SizedGeneralPurpose {
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
    pub fn operator_suffix(&self) -> &'static str {
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
}

impl std::ops::Drop for RegisterAllocationGuard {
    fn drop(&mut self) {
        self.free_channel
            .send(self.reg)
            .expect("register allocation guard outlives allocator");
    }
}

#[derive(Debug)]
pub struct GPRegisterAllocator {
    sender: mpsc::SyncSender<SizedGeneralPurpose>,
    recv: mpsc::Receiver<SizedGeneralPurpose>,
    registers: Vec<SizedGeneralPurpose>,
}

impl GPRegisterAllocator {
    #[allow(dead_code)]
    pub fn new(registers: Vec<SizedGeneralPurpose>) -> Self {
        let (sender, recv) = mpsc::sync_channel(1);

        Self {
            sender,
            recv,
            registers,
        }
    }

    /// Allocates a register for the duration of the life of closure.
    pub fn allocate_then<F, R>(&mut self, f: F) -> R
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
        let (sender, recv) = mpsc::sync_channel(1);

        Self {
            sender,
            recv,
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

#[cfg(test)]
mod tests {
    use crate::codegen::machine::arch::x86_64;
    use crate::codegen::register::Register;

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
        let initial_len = allocator.registers.len();

        // allocator pool should decrease by 1 while allocated in scope.
        allocator
            .allocate_then(|allocator, _| assert_eq!(initial_len - 1, allocator.registers.len()));

        // register should be freed on scope exit.
        assert_eq!(initial_len, allocator.registers.len());
    }
}
