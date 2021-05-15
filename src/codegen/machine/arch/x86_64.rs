use crate::codegen::machine::arch::TargetArchitecture;
use crate::codegen::register_allocation::{Register, RegisterAllocatable};

/// X86_64 represents the x86_64 bit machine target.
pub struct X86_64;

impl TargetArchitecture for X86_64 {}

#[derive(Debug, Clone)]
pub struct RegisterAllocator {
    registers: Vec<Register>,
    allocated: Vec<bool>,
}

impl Default for RegisterAllocator {
    fn default() -> Self {
        Self {
            registers: vec![
                Register::from("%r8"),
                Register::from("%r9"),
                Register::from("%r10"),
                Register::from("%rx11"),
            ],
            allocated: [false].iter().cycle().take(4).copied().collect(),
        }
    }
}

impl RegisterAllocator {
    /// Optionally returns a register, by Id, if it exists.
    pub fn register(&self, idx: usize) -> Option<Register> {
        self.registers.get(idx).copied()
    }
}

impl RegisterAllocatable for RegisterAllocator {
    fn register_ids() -> Vec<&'static str> {
        vec!["%r8", "%r9", "%r10", "%r11"]
    }

    /// Finds the first unallocated register, if one is found it is returned
    /// as an option.
    fn allocate_mut(&mut self) -> Option<usize> {
        if let Some(idx) = get_unallocated_register(self) {
            self.allocated[idx] = true;
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
        if let Some(alloc) = self.allocated.get_mut(idx) {
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
        self.allocated = [false].iter().cycle().copied().take(4).collect();
    }

    fn free_all(mut self) -> Self {
        self.free_all_mut();
        self
    }
}

/// Finds the first unallocated register, if any, If any are available the offset is returned.
fn get_unallocated_register(ra: &RegisterAllocator) -> Option<usize> {
    ra.allocated
        .iter()
        .enumerate()
        .filter_map(|(idx, allocated)| if *allocated { None } else { Some(idx) })
        .next()
}
