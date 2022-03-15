#[derive(Debug, Clone)]
pub struct Stack<T, const N: usize> {
    head: usize,
    data: [T; N],
}

// Generic constants
impl<T, const N: usize> Stack<T, N> {
    /// Represents the minimum index of the stack.
    const MIN: usize = 0;

    /// Represents the maximum index of the stack.
    const MAX: usize = N - 1;
}

impl<T, const N: usize> Stack<T, N> {
    /// Stack initializer type.
    pub fn new(data: [T; N]) -> Self {
        Self { head: 0, data }
    }
}

impl<T: Default, const N: usize> Stack<T, N> {
    pub fn empty(&self) -> bool {
        self.head == Self::MIN
    }

    pub fn full(&self) -> bool {
        self.head == Self::MAX
    }

    pub fn push_mut(&mut self, val: T) {
        if self.full() {
            panic!("stack overflow...")
        } else {
            let idx = self.head;
            self.data[idx] = val;
            self.head = idx + 1
        }
    }

    pub fn pop_mut(&mut self) -> Option<T> {
        use core::mem;

        if self.empty() {
            None
        } else {
            self.head -= 1;
            let last = mem::take(&mut self.data[self.head]);

            Some(last)
        }
    }
}

impl<T, const N: usize> AsRef<[T]> for Stack<T, N> {
    fn as_ref(&self) -> &[T] {
        &self.data[0..self.head]
    }
}

impl<T, const N: usize, const M: usize> PartialEq<[T; M]> for Stack<T, N>
where
    T: PartialEq,
{
    fn eq(&self, other: &[T; M]) -> bool {
        self.data.iter().eq(other.iter())
    }
}

impl<T, const N: usize> PartialEq<&[T]> for Stack<T, N>
where
    T: PartialEq,
{
    fn eq(&self, other: &&[T]) -> bool {
        self.data.iter().eq(other.iter())
    }
}

impl<T: Copy + Default, const N: usize> Default for Stack<T, N> {
    fn default() -> Self {
        Self {
            head: 0,
            data: [T::default(); N],
        }
    }
}
