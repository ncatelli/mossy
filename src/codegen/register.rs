/// Register implements the methods for register to store a value of a given size.
pub trait Register<R, W>
where
    Self: Copy,
{
    fn read(&self) -> R;
    fn write(self, value: W) -> Self;
    fn with_value(self, value: W) -> Self;
}

/// GeneralPurpose register represents a string representable register that can
/// be used both by allocators and by code generation.
#[derive(Debug, Clone, Copy)]
pub struct GeneralPurpose<V> {
    repr: &'static str,
    inner: V,
}

impl<V> GeneralPurpose<V>
where
    V: Default,
{
    /// instantiates a register with the str representation passed as `repr`.
    pub fn new(repr: &'static str) -> Self {
        Self {
            repr,
            inner: <V>::default(),
        }
    }
}

impl<V> GeneralPurpose<V> {
    /// returns the string representation of the register.
    pub fn id(&self) -> &'static str {
        self.repr
    }
}

impl<V> Register<V, V> for GeneralPurpose<V>
where
    V: Copy,
{
    fn read(&self) -> V {
        self.inner
    }

    fn write(mut self, value: V) -> Self {
        self.inner = value;
        self
    }

    fn with_value(mut self, value: V) -> Self {
        self.inner = value;
        self
    }
}

impl<V> From<&'static str> for GeneralPurpose<V>
where
    V: Default,
{
    fn from(repr: &'static str) -> Self {
        Self::new(repr)
    }
}

impl<V> std::fmt::Display for GeneralPurpose<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.repr)
    }
}
