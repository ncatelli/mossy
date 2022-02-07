use std::ops::Range;

pub use crate::stage::type_check::ast::ByteSized;

pub mod register;
use register::WidthFormatted;

/// Provides an enumerable type for a location that can be either a
/// register or offset.
#[derive(Debug, Clone, Copy)]
pub(crate) enum RegisterOrOffset<GP>
where
    GP: WidthFormatted,
{
    Register(GP),
    Offset(isize),
}

impl<GP> WidthFormatted for RegisterOrOffset<GP>
where
    GP: WidthFormatted,
    <GP as register::WidthFormatted>::Output: std::string::ToString,
{
    type Output = String;

    fn fmt_with_operand_width(&self, width: register::OperandWidth) -> Self::Output {
        (&self).fmt_with_operand_width(width)
    }
}

impl<GP> WidthFormatted for &RegisterOrOffset<GP>
where
    GP: WidthFormatted,
    <GP as register::WidthFormatted>::Output: std::string::ToString,
{
    type Output = String;

    fn fmt_with_operand_width(&self, width: register::OperandWidth) -> Self::Output {
        match self {
            RegisterOrOffset::Register(reg) => reg.fmt_with_operand_width(width).to_string(),
            RegisterOrOffset::Offset(offset) => {
                format!(
                    "{}({})",
                    offset,
                    register::BasePointerRegister
                        .fmt_with_operand_width(register::OperandWidth::QuadWord)
                )
            }
        }
    }
}

#[derive(Debug)]
pub(crate) struct SysVAllocator {
    pub(crate) accumulator: register::Accumulator,
    pub(crate) general_purpose_reg_allocator: register::GPRegisterAllocator,
    pub(crate) parameter_stack_offsets: Vec<Range<isize>>,
    pub(crate) local_stack_offsets: Vec<Range<isize>>,
}

impl SysVAllocator {
    pub fn new(general_purpose_reg_allocator: register::GPRegisterAllocator) -> Self {
        Self {
            accumulator: register::Accumulator,
            general_purpose_reg_allocator,
            parameter_stack_offsets: vec![],
            local_stack_offsets: vec![],
        }
    }
}

impl SysVAllocator {
    /// Handles the allocation of, and corresponding free of a general-purpose
    /// register, which is passed to a given closure. The return of the closure
    /// is returned after freeing the register.
    pub fn allocate_general_purpose_register_then<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self, &mut RegisterOrOffset<&register::GeneralPurposeRegister>) -> R,
    {
        self.general_purpose_reg_allocator
            .allocate()
            .map(|guard| {
                let ret_val = f(self, &mut RegisterOrOffset::Register(guard.borrow_inner()));
                ret_val
            })
            .expect("unable to allocate register")
    }

    pub fn safe_and_zero_accumulator_then<F>(&mut self, f: F) -> Vec<String>
    where
        F: FnOnce(&mut Self) -> Vec<String>,
    {
        let ret_val = f(self);
        vec![
            format!(
                "\tpushq\t{}\n",
                self.accumulator
                    .fmt_with_operand_width(register::OperandWidth::QuadWord)
            ),
            format!(
                "\tandq\t$0, {}\n",
                self.accumulator
                    .fmt_with_operand_width(register::OperandWidth::QuadWord)
            ),
        ]
        .into_iter()
        .chain(ret_val.into_iter())
        .chain(vec![format!(
            "\tpopq\t{}\n",
            self.accumulator
                .fmt_with_operand_width(register::OperandWidth::QuadWord)
        )])
        .collect()
    }

    pub fn allocate_and_zero_general_purpose_register_then<F>(&mut self, f: F) -> Vec<String>
    where
        F: FnOnce(
            &mut Self,
            &mut RegisterOrOffset<&register::GeneralPurposeRegister>,
        ) -> Vec<String>,
    {
        self.general_purpose_reg_allocator
            .allocate()
            .map(|guard| {
                let borrowed_reg = guard.borrow_inner();
                let ret_val = f(self, &mut RegisterOrOffset::Register(borrowed_reg));
                vec![format!(
                    "\tandq\t$0, {}\n",
                    borrowed_reg.fmt_with_operand_width(register::OperandWidth::QuadWord)
                )]
                .into_iter()
                .chain(ret_val.into_iter())
                .collect()
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

    pub fn get_parameter_slot_offset(&self, slot: usize) -> Option<isize> {
        self.parameter_stack_offsets
            .get(slot)
            .map(|slot_offsets| slot_offsets.start)
    }

    pub fn get_local_slot_offset(&self, slot: usize) -> Option<isize> {
        self.local_stack_offsets
            .get(slot)
            .map(|slot_offsets| slot_offsets.start)
    }

    pub fn parameter_passing_target_for_slot(
        &self,
        slot: usize,
    ) -> Option<register::FunctionPassingRegisters> {
        use register::FunctionPassingRegisters::*;
        match slot {
            0 => Some(DI),
            1 => Some(SI),
            2 => Some(D),
            3 => Some(C),
            4 => Some(R8),
            5 => Some(R9),
            _ => None,
        }
    }

    fn insert_parameter_slot_offset(&mut self, slot: usize, offset: Range<isize>) -> Range<isize> {
        self.parameter_stack_offsets.insert(slot, offset.clone());
        offset
    }

    pub fn calculate_and_insert_parameter_offset<S>(
        &mut self,
        slot: usize,
        sized: S,
    ) -> Option<Range<isize>>
    where
        S: ByteSized,
    {
        self.calculate_and_insert_parameter_offset_with_cnt(slot, sized, 1)
    }

    pub fn calculate_and_insert_parameter_offset_with_cnt<S>(
        &mut self,
        slot: usize,
        sized: S,
        cnt: usize,
    ) -> Option<Range<isize>>
    where
        S: ByteSized,
    {
        let parameter_stack_offset = self.calculate_parameter_offset_for_slot(slot, sized, cnt)?;
        self.insert_parameter_slot_offset(slot, parameter_stack_offset.clone());
        Some(parameter_stack_offset)
    }

    pub fn calculate_parameter_offset_for_slot<S>(
        &self,
        slot: usize,
        sized: S,
        cnt: usize,
    ) -> Option<Range<isize>>
    where
        S: ByteSized,
    {
        let rounded_size = if slot < 6 {
            // round for stack allocation
            round_sized_type_for_local_offset(sized.size() * cnt)
        } else {
            // already on the stack
            8 * cnt
        };
        match slot {
            0 => Some(-(rounded_size as isize)..0),
            1..=5 => self
                .parameter_stack_offsets
                .get(slot - 1)
                .map(|slot_offsets| slot_offsets.start)
                .map(|slot_end_offset| {
                    let slot_start_offset = slot_end_offset - (rounded_size as isize);
                    slot_start_offset..slot_end_offset
                }),
            6 => Some(16..(rounded_size as isize)),
            non_base_stack_slot => self
                .parameter_stack_offsets
                .get(non_base_stack_slot - 1)
                .map(|slot_offsets| slot_offsets.start)
                .map(|slot_end_offset| {
                    let slot_start_offset = slot_end_offset + (rounded_size as isize);
                    slot_start_offset..slot_end_offset
                }),
        }
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

        let slot_end_offset = match (slot == 0, self.parameter_stack_offsets.is_empty()) {
            (true, true) => None,
            // start from the last stack slot of the parameters local stack.
            (true, false) => self
                .parameter_stack_offsets
                .iter()
                // strip of any parameters that are pushed above rbp
                .filter(|r| r.start.is_negative())
                .last()
                .map(|slot_offsets| slot_offsets.start),
            // reference the last offset
            (false, _) => self
                .local_stack_offsets
                .get(slot - 1)
                .map(|slot_offsets| slot_offsets.start),
        }
        .unwrap_or(0);

        let slot_start_offset = slot_end_offset - (rounded_size as isize);

        Some(slot_start_offset..slot_end_offset)
    }

    fn insert_local_slot_offset(&mut self, slot: usize, offset: Range<isize>) -> Range<isize> {
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
        self.insert_local_slot_offset(slot, local_offset.clone());
        Some(local_offset)
    }

    pub fn top_of_local_stack(&self) -> isize {
        self.local_stack_offsets
            .iter()
            .chain(self.parameter_stack_offsets.iter())
            .map(|offset| offset.start)
            .filter(|&start| start.is_negative())
            .min()
            .unwrap_or(0)
    }

    pub fn align_stack_pointer(&self, stack_end: isize) -> isize {
        (stack_end.abs() + 15) & !15
    }

    pub fn align_post_call_stack(&self, arg_cnt: usize) -> Option<usize> {
        if arg_cnt > 6 {
            Some((arg_cnt - 6) * 8)
        } else {
            None
        }
    }
}

#[allow(dead_code)]
const fn round_sized_type_for_local_offset(size: usize) -> usize {
    match size {
        size if size > 4 => size,
        _ => 4,
    }
}
