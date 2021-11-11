use crate::codegen::register::{AddressWidth, Register};
use std::sync::mpsc;

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

    fn allocate(&mut self) -> Option<RegisterAllocationGuard> {
        let reg = self.available.try_recv().ok()?;

        Some(RegisterAllocationGuard::new(self.freed.clone(), reg))
    }

    /// Allocates a register for the duration of the life of closure.
    pub fn allocate_then<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self, &mut SizedGeneralPurpose) -> R,
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
