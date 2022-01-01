pub(crate) fn pad_to_le_64bit_array<I>(bytes: I) -> [u8; 8]
where
    I: IntoIterator<Item = u8>,
{
    bytes
        .into_iter()
        .chain(core::iter::repeat(0u8))
        .take(8)
        .enumerate()
        .fold([0u8; 8], |mut acc, (idx, byte)| {
            acc[idx] = byte;
            acc
        })
}
