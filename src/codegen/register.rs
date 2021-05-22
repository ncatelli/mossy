/// Register implements the methods for register to store a value of a given size.
pub trait Register<R, W>
where
    Self: Copy,
{
    fn read(&self) -> R;
    fn write(self, value: W) -> Self;
    fn with_value(self, value: W) -> Self;
}
