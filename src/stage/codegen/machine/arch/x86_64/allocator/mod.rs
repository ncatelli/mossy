pub mod register;

pub(crate) struct Allocator {
    pub(crate) general_purpose_reg_allocator: register::GPRegisterAllocator,
}

impl Allocator {
    pub fn new(general_purpose_reg_allocator: register::GPRegisterAllocator) -> Self {
        Self {
            general_purpose_reg_allocator,
        }
    }
}

impl Allocator {
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
