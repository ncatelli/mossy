use crate::machine::arch::*;

pub trait RegisterAllocatable {
    fn register_ids() -> Vec<&'static str>;
}

impl RegisterAllocatable for X86_64 {
    fn register_ids() -> Vec<&'static str> {
        vec!["%r8", "%r9", "%r10", "%r11"]
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Register {
    id: &'static str,
}

impl Register {
    pub fn new(id: &'static str) -> Self {
        Self { id }
    }
}

impl From<&'static str> for Register {
    fn from(id: &'static str) -> Self {
        Self { id }
    }
}

#[derive(Debug, Clone)]
pub struct RegisterAllocator<A>
where
    A: TargetArchitecture + RegisterAllocatable,
{
    architecture: std::marker::PhantomData<A>,
    registers: Vec<Register>,
    allocated: Vec<bool>,
}

impl<A> RegisterAllocator<A>
where
    A: TargetArchitecture + RegisterAllocatable,
{
    /// new instantiates a new register allocator for a given register
    /// allocatable TargetArchitecture.
    pub fn new() -> Self {
        let registers: Vec<Register> = <A>::register_ids()
            .iter()
            .map(|&id| Register::from(id))
            .collect();

        let allocated: Vec<bool> = [false]
            .iter()
            .cycle()
            .copied()
            .take(registers.len())
            .collect();

        Self {
            architecture: std::marker::PhantomData,
            registers,
            allocated,
        }
    }
}

impl<A> RegisterAllocator<A>
where
    A: TargetArchitecture + RegisterAllocatable,
{
    /// Optionally returns a register, by Id, if it exists.
    pub fn register(&self, idx: usize) -> Option<Register> {
        self.registers.get(idx).copied()
    }

    /// Finds the first unallocated register, if one is found it is returned
    /// as an option.
    pub fn allocate_mut(&mut self) -> Option<usize> {
        if let Some(idx) = get_unallocated_register(self) {
            self.allocated[idx] = true;
            Some(idx)
        } else {
            None
        }
    }

    /// Finds the first unallocated register, if one is found it is returned
    /// as an option.
    pub fn allocate(mut self) -> (Self, Option<usize>) {
        let allocated_id = self.allocate_mut();
        (self, allocated_id)
    }

    pub fn free_mut(&mut self, idx: usize) -> Option<usize> {
        if let Some(alloc) = self.allocated.get_mut(idx) {
            *alloc = false;
            Some(idx)
        } else {
            None
        }
    }

    pub fn free(mut self, idx: usize) -> (Self, Option<usize>) {
        let idx = self.free_mut(idx);
        (self, idx)
    }

    pub fn free_all_mut(&mut self) {
        self.allocated = [false]
            .iter()
            .cycle()
            .copied()
            .take(self.registers.len())
            .collect::<Vec<bool>>();
    }

    pub fn free_all(mut self) -> Self {
        self.free_all_mut();
        self
    }
}

/// Finds the first unallocated register, if any, If any are available the offset is returned.
fn get_unallocated_register<A>(ra: &RegisterAllocator<A>) -> Option<usize>
where
    A: TargetArchitecture + RegisterAllocatable,
{
    ra.allocated
        .iter()
        .enumerate()
        .filter_map(|(idx, allocated)| if *allocated { None } else { Some(idx) })
        .next()
}
