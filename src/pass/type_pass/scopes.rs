use crate::ast::Type;

// Alias for a hashmap of String/Type
pub type Scope = std::collections::HashMap<String, Type>;

/// Provides a stack of hashmaps for tracking scopes
#[derive(Default)]
pub struct ScopeStack {
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

    /// Defines a new variable in place.
    pub fn define_mut(&mut self, id: &str, ty: Type) {
        self.scopes
            .last_mut()
            .map(|scope| scope.insert(id.to_string(), ty));
    }

    /// looks up variable in place.
    pub fn lookup(&self, id: &str) -> Option<Type> {
        self.scopes
            .iter()
            .rev()
            .find(|scope| scope.get(id).is_some())
            .and_then(|scope| scope.get(id))
            .cloned()
    }
}
