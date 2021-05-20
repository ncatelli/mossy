use crate::ast;

pub mod machine;
mod register;

#[derive(Default, Debug, Clone)]
pub struct SymbolTable {
    globals: std::collections::HashMap<String, Option<u8>>,
}

impl SymbolTable {
    pub fn declare_global(&mut self, identifier: &str) {
        self.globals.insert(identifier.to_string(), None);
    }

    pub fn assign_global(&mut self, identifier: &str, value: u8) -> Result<u8, String> {
        if self.globals.contains_key(identifier) {
            self.globals.insert(identifier.to_string(), Some(value));
            Ok(value)
        } else {
            Err(format!("undeclared variable: {}", identifier))
        }
    }
}

/// CodeGenerationErr represents an error stemming from the CodeGenerator's
/// `generate` method, capturing any potential point of breakdown withing the
/// code generation process.
#[derive(Clone, PartialEq)]
pub enum CodeGenerationErr {
    Unspecified(String),
}

impl std::fmt::Debug for CodeGenerationErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CodeGenerationErr::Unspecified(e) => {
                write!(f, "unspecified code generation err: {}", e)
            }
        }
    }
}

/// CodeGenerator defines the generate method, returning a string representation
/// of all generated instructions or an error.
pub trait CodeGenerator {
    fn generate(
        self,
        symboltable: &mut SymbolTable,
        input: ast::StmtNode,
    ) -> Result<Vec<String>, CodeGenerationErr>;
}
