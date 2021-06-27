use crate::codegen::register::{AddressWidth, Register};

pub const GPREGISTERS: [SizedGeneralPurpose; 8] = [
    SizedGeneralPurpose::QuadWord("r8"),
    SizedGeneralPurpose::QuadWord("r9"),
    SizedGeneralPurpose::QuadWord("r10"),
    SizedGeneralPurpose::QuadWord("r11"),
    SizedGeneralPurpose::QuadWord("r12"),
    SizedGeneralPurpose::QuadWord("r13"),
    SizedGeneralPurpose::QuadWord("r14"),
    SizedGeneralPurpose::QuadWord("r15"),
];

#[derive(Debug, Clone, Copy, PartialEq)]
#[allow(dead_code)]
pub enum SizedGeneralPurpose {
    QuadWord(&'static str),
    DoubleWord(&'static str),
    Word(&'static str),
    Byte(&'static str),
}

impl AddressWidth for SizedGeneralPurpose {
    fn bits(&self) -> usize {
        match self {
            SizedGeneralPurpose::QuadWord(_) => 64,
            SizedGeneralPurpose::DoubleWord(_) => 32,
            SizedGeneralPurpose::Word(_) => 16,
            SizedGeneralPurpose::Byte(_) => 8,
        }
    }
}

impl crate::codegen::register::Register<u64> for SizedGeneralPurpose {
    /// returns the string representation of the register.
    fn id(&self) -> &'static str {
        match self {
            SizedGeneralPurpose::QuadWord(id) => id,
            SizedGeneralPurpose::DoubleWord(id) => id,
            SizedGeneralPurpose::Word(id) => id,
            SizedGeneralPurpose::Byte(id) => id,
        }
    }
}

impl SizedGeneralPurpose {
    pub fn operator_suffix(&self) -> &'static str {
        match self {
            SizedGeneralPurpose::QuadWord(_) => "q",
            SizedGeneralPurpose::DoubleWord(_) => "l",
            SizedGeneralPurpose::Word(_) => "w",
            SizedGeneralPurpose::Byte(_) => "b",
        }
    }
}

impl std::fmt::Display for SizedGeneralPurpose {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let repr = self.id();
        let register_suffix = match self {
            SizedGeneralPurpose::QuadWord(_) => "",
            SizedGeneralPurpose::DoubleWord(_) => "d",
            SizedGeneralPurpose::Word(_) => "w",
            SizedGeneralPurpose::Byte(_) => "b",
        };

        write!(f, "%{}{}", repr, register_suffix)
    }
}
