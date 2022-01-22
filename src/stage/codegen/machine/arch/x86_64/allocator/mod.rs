use std::ops::Range;

pub use crate::stage::slotted_type_check::ast::ByteSized;

pub mod register;

#[derive(Debug)]
pub(crate) struct SysVAllocator {
    pub(crate) general_purpose_reg_allocator: register::GPRegisterAllocator,
    pub(crate) local_stack_offsets: Vec<Range<isize>>,
}

impl SysVAllocator {
    pub fn new(general_purpose_reg_allocator: register::GPRegisterAllocator) -> Self {
        Self {
            general_purpose_reg_allocator,
            local_stack_offsets: vec![],
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

    pub fn allocate_new_local_stack_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let new_scope = vec![];
        let old_scope = std::mem::replace(&mut self.local_stack_offsets, new_scope);

        let ret_val = f(self);
        let _ = std::mem::replace(&mut self.local_stack_offsets, old_scope);

        ret_val
    }

    pub fn get_slot_offset(&self, slot: usize) -> Option<isize> {
        self.local_stack_offsets
            .get(slot)
            .map(|slot_offsets| slot_offsets.start)
    }

    /// Calculates an exclusive range of offsets for a given slot and type,
    /// returning None if preceeding slots have not been allocated.
    pub fn calculate_local_offset_for_slot<S>(
        &self,
        slot: usize,
        sized: S,
        cnt: usize,
    ) -> Option<Range<isize>>
    where
        S: ByteSized,
    {
        let rounded_size = round_sized_type_for_local_offset(sized.size() * cnt);

        let slot_end_offset = if slot == 0 {
            None
        } else {
            self.local_stack_offsets
                .get(slot - 1)
                .map(|slot_offsets| slot_offsets.start)
        }
        .unwrap_or(0);

        let slot_start_offset = -(slot_end_offset + (rounded_size as isize));

        Some(slot_start_offset..slot_end_offset)
    }

    pub fn insert_slot_offset(&mut self, slot: usize, offset: Range<isize>) -> Range<isize> {
        self.local_stack_offsets.insert(slot, offset.clone());
        offset
    }

    /// Provides a convenient wrapper for calculation of and insertion of a type into a local offset.
    pub fn calculate_and_insert_local_offset<S>(
        &mut self,
        slot: usize,
        sized: S,
    ) -> Option<Range<isize>>
    where
        S: ByteSized,
    {
        self.calculate_and_insert_local_offset_with_cnt(slot, sized, 1)
    }

    /// Provides a convenient wrapper for calculation of and insertion of a type into a local offset.
    pub fn calculate_and_insert_local_offset_with_cnt<S>(
        &mut self,
        slot: usize,
        sized: S,
        cnt: usize,
    ) -> Option<Range<isize>>
    where
        S: ByteSized,
    {
        let local_offset = self.calculate_local_offset_for_slot(slot, sized, cnt)?;
        self.insert_slot_offset(slot, local_offset.clone());
        Some(local_offset)
    }

    pub fn align_stack_pointer(&self, stack_end: isize) -> isize {
        (stack_end.abs() + 15) & !15
    }
}

#[allow(dead_code)]
const fn round_sized_type_for_local_offset(size: usize) -> usize {
    match size {
        size if size > 4 => size,
        _ => 4,
    }
}
