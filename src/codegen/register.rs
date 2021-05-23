/// Represents a bit sized type
pub trait AddressWidth {
    fn bits(&self) -> usize;
}

macro_rules! impl_address_width_with_bits {
    ($($t:ty => $width:literal,)*) => {
        $(
            impl AddressWidth for $t {
                fn bits(&self) -> usize {
                    $width
                }
            }
        )*
    };
}

impl_address_width_with_bits!(
    u16 => 16,
    u32 => 32,
    u64 => 64,
);

/// Register implements the methods for register to store a value of a given size.
pub trait Register<A>
where
    Self: Copy,
    A: AddressWidth,
{
    fn id(&self) -> &'static str;
}
