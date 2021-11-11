use crate::ast::Type;

pub type Scope = std::collections::HashMap<String, Type>;

#[derive(Default)]
pub struct ScopeStack {
    scopes: Vec<Scope>,
}

impl ScopeStack {
    pub fn new() -> Self {
        Self { scopes: vec![] }
    }

    pub fn push_mut(&mut self, scope: Scope) {
        self.scopes.push(scope);
    }

    pub fn push_new_scope_mut(&mut self) {
        self.scopes.push(Scope::new());
    }

    pub fn pop_scope_mut(&mut self) {
        self.scopes.pop();
    }

    pub fn define_mut(&mut self, id: &str, ty: Type) {
        self.scopes
            .last_mut()
            .map(|scope| scope.insert(id.to_string(), ty));
    }

    pub fn lookup(&self, id: &str) -> Option<Type> {
        self.scopes
            .iter()
            .rev()
            .find(|scope| scope.get(id).is_some())
            .and_then(|scope| scope.get(id))
            .copied()
    }
}
