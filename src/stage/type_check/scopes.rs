use crate::stage::type_check::ast::Type;

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

/// Defines the locality of a variable in a given scope.
#[derive(Debug, Clone, Copy)]
pub enum Locality {
    Global,
    // Locally defined variable containing a local variable slot id.
    Local(usize),
    // Function parameter parameter slot id.
    Parameter(usize),
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
    pub locality: Locality,
}

impl DeclarationMetadata {
    fn new(ty: Type, kind: Kind, locality: Locality) -> Self {
        Self {
            r#type: ty,
            elems: kind.array_elems(),
            locality,
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
    local_slots: Vec<String>,
    parameter_slots: Vec<String>,
    symbols: std::collections::HashMap<String, DeclarationMetadata>,
}

impl Scope {
    pub fn ordered_local_declarations(&self) -> Vec<(Type, usize)> {
        self.local_slots
            .iter()
            .map(|id| {
                self.symbols
                    .get(id.as_str())
                    .map(|dm| (dm.r#type.clone(), dm.elems.unwrap_or(1)))
            })
            .flatten()
            .collect()
    }

    pub fn ordered_parameter_declarations(&self) -> Vec<Type> {
        self.local_slots
            .iter()
            .map(|id| self.symbols.get(id.as_str()).map(|dm| (dm.r#type.clone())))
            .flatten()
            .collect()
    }
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

    pub fn declare_global_mut(&mut self, id: &str, ty: Type, kind: Kind) {
        self.scopes.first_mut().map(|scope| {
            scope.symbols.insert(
                id.to_string(),
                DeclarationMetadata::new(ty, kind, Locality::Global),
            )
        });
    }

    pub fn declare_parameter_mut(&mut self, id: &str, ty: Type, kind: Kind) -> usize {
        self.scopes
            .last_mut()
            .map(|scope| {
                let slot_id = scope.parameter_slots.len();

                scope.parameter_slots.push(id.to_string());
                scope.symbols.insert(
                    id.to_string(),
                    DeclarationMetadata::new(ty, kind, Locality::Parameter(slot_id)),
                );

                slot_id
            })
            .expect("attempted to allocate local variable on non-local scope")
    }

    pub fn declare_local_mut(&mut self, id: &str, ty: Type, kind: Kind) -> usize {
        self.scopes
            .last_mut()
            .map(|scope| {
                let slot_id = scope.local_slots.len();

                scope.local_slots.push(id.to_string());
                scope.symbols.insert(
                    id.to_string(),
                    DeclarationMetadata::new(ty, kind, Locality::Local(slot_id)),
                );

                slot_id
            })
            .expect("attempted to allocate local variable on non-local scope")
    }

    pub fn local_scope(&self) -> Option<&Scope> {
        self.scopes.last()
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
