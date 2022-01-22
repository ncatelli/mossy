pub mod register;

pub(crate) struct SysVAllocator {
    pub(crate) general_purpose_reg_allocator: register::GPRegisterAllocator,
}

impl SysVAllocator {
    pub fn new(general_purpose_reg_allocator: register::GPRegisterAllocator) -> Self {
        Self {
            general_purpose_reg_allocator,
        }
    }
}

impl SysVAllocator {
    pub fn allocate_gp_register_then<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self, &register::GeneralPurposeRegister) -> R,
    {
        self.general_purpose_reg_allocator
            .allocate()
            .map(|guard| {
                let ret_val = f(self, guard.borrow_inner());
                ret_val
            })
            .expect("unable to allocate register")
    }
}

const fn round_sized_type_for_local_offset(size: usize) -> usize {
    match size {
        size if size > 4 => size,
        _ => 4,
    }
}
