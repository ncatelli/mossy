#[derive(Debug)]
pub(crate) struct Stack<'a, T> {
    head: usize,
    capacity: usize,
    data: &'a mut [T],
}

impl<'a, T> Stack<'a, T> {
    const MIN: usize = 0;
}

impl<'a, T> Stack<'a, T> {
    /// Stack initializer type.
    pub fn new(data: &'a mut [T]) -> Self {
        Self {
            head: 0,
            capacity: usize::MAX,
            data,
        }
    }

    #[allow(unused)]
    pub fn with_capacity(mut self, capacity: usize) -> Self {
        self.capacity = capacity;
        self
    }

    pub fn full(&self) -> bool {
        self.capacity <= self.head
    }

    pub fn empty(&self) -> bool {
        self.head == Self::MIN
    }

    pub fn push_mut(&mut self, val: T) {
        if self.full() {
            panic!("stack overflow")
        } else {
            let idx = self.head;
            self.data[idx] = val;
            self.head = idx + 1
        }
    }
}

impl<'a, T: Default> Stack<'a, T> {
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

impl<'a, T> AsRef<[T]> for Stack<'a, T> {
    fn as_ref(&self) -> &[T] {
        &self.data[0..self.head]
    }
}

impl<'a, T, const N: usize> PartialEq<[T; N]> for Stack<'a, T>
where
    T: PartialEq,
{
    fn eq(&self, other: &[T; N]) -> bool {
        self.data.iter().eq(other.iter())
    }
}

impl<'a, T> PartialEq<&[T]> for Stack<'a, T>
where
    T: PartialEq,
{
    fn eq(&self, other: &&[T]) -> bool {
        self.data.iter().eq(other.iter())
    }
}
