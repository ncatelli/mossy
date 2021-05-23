use crate::codegen::register::{AddressWidth, Register};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u64)]
pub enum GPRegisterMask {
    QuadWord = u64::MAX,
    DoubleWord = u32::MAX as u64,
    Word = u16::MAX as u64,
    Byte = u8::MAX as u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GPRegister {
    id: &'static str,
    allocation_mask: u64,
}

impl GPRegister {
    pub fn new(id: &'static str, allocation_mask: GPRegisterMask) -> Self {
        Self {
            id,
            allocation_mask: allocation_mask as u64,
        }
    }

    pub fn operator_suffix(&self) -> &'static str {
        match self.allocation_mask {
            am if am > (GPRegisterMask::DoubleWord as u64) => "q",
            am if am > (GPRegisterMask::Word as u64) => "l",
            am if am > (GPRegisterMask::Byte as u64) => "w",
            _ => "b",
        }
    }
}

impl Register<u64> for GPRegister {
    /// returns the string representation of the register.
    fn id(&self) -> &'static str {
        self.id
    }
}

impl AddressWidth for GPRegister {
    fn bits(&self) -> usize {
        64
    }
}

impl std::fmt::Display for GPRegister {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let repr = self.id();
        let register_suffix = self.operator_suffix();

        write!(f, "%{}{}", repr, register_suffix)
    }
}

#[derive(Debug, Clone)]
pub struct GPRegisterAllocator {
    registers: Vec<GPRegister>,
}

impl GPRegisterAllocator {
    #[allow(dead_code)]
    pub fn new(registers: Vec<GPRegister>) -> Self {
        Self { registers }
    }

    /// Allocates a register for the duration of the life of closure.
    pub fn allocate_then<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self, &mut GPRegister) -> R,
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
        Self {
            registers: vec![
                GPRegister::new("r8", GPRegisterMask::QuadWord),
                GPRegister::new("r9", GPRegisterMask::QuadWord),
                GPRegister::new("r10", GPRegisterMask::QuadWord),
                GPRegister::new("r11", GPRegisterMask::QuadWord),
                GPRegister::new("r12", GPRegisterMask::QuadWord),
                GPRegister::new("r13", GPRegisterMask::QuadWord),
                GPRegister::new("r14", GPRegisterMask::QuadWord),
                GPRegister::new("r15", GPRegisterMask::QuadWord),
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
