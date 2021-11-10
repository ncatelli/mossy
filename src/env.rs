use crate::ast::kinded::Kind;
type Scope = std::collections::HashMap<String, Kind>;

#[derive(Default)]
pub struct Scopes {
    scopes: Vec<Scope>,
}

impl Scopes {
    pub fn new() -> Self {
        Self { scopes: vec![] }
    }

    pub fn push(mut self, scope: Scope) -> Scopes {
        self.scopes.push(scope);
        self
    }

    pub fn push_mut(&mut self, scope: Scope) {
        self.scopes.push(scope);
    }

    pub fn define_mut(&mut self, id: String, kind: Kind) {
        self.scopes.last_mut().map(|scope| scope.insert(id, kind));
    }

    pub fn lookup(&self, id: String) -> Option<Kind> {
        self.scopes
            .iter()
            .rev()
            .find(|scope| scope.get(&id).is_some())
            .and_then(|scope| scope.get(&id))
            .copied()
    }
}
