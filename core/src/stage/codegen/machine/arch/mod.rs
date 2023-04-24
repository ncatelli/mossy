pub mod x86_64;

/// TargetArchitecture is a bare trait used for signalling that a type
/// represents an architecture that cant be supported as a compiler target.
pub trait TargetArchitecture {}

/// AvailableArchitectures represents each of the supported architectures in
/// an enumerable format.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AvailableArchitectures {
    X86_64,
}

impl From<AvailableArchitectures> for Box<dyn TargetArchitecture> {
    fn from(src: AvailableArchitectures) -> Self {
        match src {
            AvailableArchitectures::X86_64 => Box::new(x86_64::X86_64),
        }
    }
}
