use crate::stage::ast::Type;

/// DeclarationMetadata contains information about a given declared variable.
/// This information currenntly includes defined size and type.
#[derive(Debug, Clone)]
pub struct DeclarationMetadata {
    pub r#type: Type,
    // if Some, implies that this is a fixed size array of a known size.
    // Otherwise it is a singular type be it a known value or pointer to a
    // value.
    pub size: Option<usize>,
}

impl DeclarationMetadata {
    pub fn new(ty: Type, size: Option<usize>) -> Self {
        Self { r#type: ty, size }
    }

    /// Returns a boolean signifying a type is a fixed size array.
    pub fn is_array(&self) -> bool {
        (matches!(self.r#type, Type::Pointer(_)) && self.size.is_some())
    }

    /// Returns a boolean signifying a type is a direct refence type.
    /// i.e. not a pointer.
    #[allow(unused)]
    pub fn is_direct_reference(&self) -> bool {
        self.is_array() || !matches!(self.r#type, Type::Pointer(_))
    }
}

// Alias for a hashmap of String/Type
pub(crate) type Scope = std::collections::HashMap<String, DeclarationMetadata>;

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
        self.scopes.push(Scope::new());
    }

    /// Pops a scope from the end of the stack.
    pub fn pop_scope_mut(&mut self) {
        self.scopes.pop();
    }

    /// Defines a new global variable in place.
    pub fn define_global_mut(&mut self, id: &str, ty: Type) {
        self.scopes
            .first_mut()
            .map(|scope| scope.insert(id.to_string(), DeclarationMetadata::new(ty, None)));
    }

    /// Defines a new global variable in place.
    pub fn define_global_with_size_mut(&mut self, id: &str, ty: Type, size: usize) {
        self.scopes
            .first_mut()
            .map(|scope| scope.insert(id.to_string(), DeclarationMetadata::new(ty, Some(size))));
    }

    /// Defines a new local variable in place.
    pub fn define_local_mut(&mut self, id: &str, ty: Type) {
        self.scopes
            .last_mut()
            .map(|scope| scope.insert(id.to_string(), DeclarationMetadata::new(ty, None)));
    }

    /// Defines a new local variable in place.
    pub fn define_local_with_size_mut(&mut self, id: &str, ty: Type, size: usize) {
        self.scopes
            .last_mut()
            .map(|scope| scope.insert(id.to_string(), DeclarationMetadata::new(ty, Some(size))));
    }

    /// looks up variable in place.
    pub fn lookup(&self, id: &str) -> Option<DeclarationMetadata> {
        self.scopes
            .iter()
            .rev()
            .find(|scope| scope.get(id).is_some())
            .and_then(|scope| scope.get(id))
            .cloned()
    }
}
