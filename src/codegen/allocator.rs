/// Represents a unique, yet reusable, id for a given allocation entity.
pub type AllocatorEntityId = usize;

/// Allocator represents any allocator that can allocate
pub trait Allocator
where
    Self: Sized,
{
    fn allocate(self) -> (Self, Option<AllocatorEntityId>);
    fn allocate_mut(&mut self) -> Option<AllocatorEntityId>;
    fn free(self, aei: usize) -> (Self, Option<AllocatorEntityId>);
    fn free_mut(&mut self, aei: usize) -> Option<AllocatorEntityId>;
    fn free_all(self) -> Self;
    fn free_all_mut(&mut self);
}
