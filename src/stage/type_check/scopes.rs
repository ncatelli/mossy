use crate::stage::ast::{ByteSized, Type};

#[derive(Debug, Clone, Copy)]
pub enum Kind {
    /// A single element of a type. (int, floating point, etc...)
    Basic,
    /// An array of n elements of a type (int[4], etc...)
    Array(usize),
}

impl Kind {
    /// If the kind is an array, return an option containing the number of
    /// elements. Otherwise return None for scalars.
    fn array_elems(&self) -> Option<usize> {
        match self {
            Kind::Basic => None,
            Kind::Array(elems) => Some(*elems),
        }
    }
}

/// DeclarationMetadata contains information about a given declared variable.
/// This information currenntly includes defined size and type.
#[derive(Debug, Clone)]
pub struct DeclarationMetadata {
    pub r#type: Type,
    // if Some, implies that this is a fixed size array of a known size.
    // Otherwise it is a singular type be it a known value or pointer to a
    // value.
    pub elems: Option<usize>,
    pub is_local: Option<isize>,
}

impl DeclarationMetadata {
    fn new(ty: Type, kind: Kind, local_offset: Option<isize>) -> Self {
        Self {
            r#type: ty,
            elems: kind.array_elems(),
            is_local: local_offset,
        }
    }

    /// Returns a boolean signifying a type is a fixed size array.
    pub fn is_array(&self) -> bool {
        (matches!(self.r#type, Type::Pointer(_)) && self.elems.is_some())
    }

    /// Returns a boolean signifying a type is a direct refence type.
    /// i.e. not a pointer.
    #[allow(unused)]
    pub fn is_direct_reference(&self) -> bool {
        self.is_array() || !matches!(self.r#type, Type::Pointer(_))
    }
}

// Alias for a hashmap of String/Type
#[derive(Debug, Default)]
pub(crate) struct Scope {
    local_offset: isize,
    symbols: std::collections::HashMap<String, DeclarationMetadata>,
}

/// Provides a stack of hashmaps for tracking scopes
#[derive(Default)]
pub(crate) struct ScopeStack {
    scopes: Vec<Scope>,
}

impl ScopeStack {
    /// Instantiates an empty scope.
    pub fn new() -> Self {
        Self { scopes: vec![] }
    }

    /// Pushes a new scope to the end of the stack.
    pub fn push_new_scope_mut(&mut self) {
        self.scopes.push(Scope::default());
    }

    /// Pops a scope from the end of the stack.
    pub fn pop_scope_mut(&mut self) {
        self.scopes.pop();
    }

    pub fn define_global_mut(&mut self, id: &str, ty: Type, kind: Kind) {
        self.scopes.first_mut().map(|scope| {
            scope
                .symbols
                .insert(id.to_string(), DeclarationMetadata::new(ty, kind, None))
        });
    }

    pub fn define_local_mut(&mut self, id: &str, ty: Type, kind: Kind) -> isize {
        let offset = -(round_sized_type_for_local_offset(ty.size()) as isize);
        self.scopes.last_mut().map(|scope| {
            scope.local_offset += offset;
            scope.symbols.insert(
                id.to_string(),
                DeclarationMetadata::new(ty, kind, Some(scope.local_offset)),
            )
        });

        offset
    }

    /// looks up variable in place.
    pub fn lookup(&self, id: &str) -> Option<DeclarationMetadata> {
        self.scopes
            .iter()
            .rev()
            .find(|scope| scope.symbols.get(id).is_some())
            .and_then(|scope| scope.symbols.get(id))
            .cloned()
    }
}

const fn round_sized_type_for_local_offset(size: usize) -> usize {
    match size {
        size if size > 4 => size,
        _ => 4,
    }
}
