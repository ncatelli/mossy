use crate::ast;

mod register_allocation;

#[derive(Clone, PartialEq)]
pub enum CompileErr {
    Unspecified(String),
}

impl std::fmt::Debug for CompileErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileErr::Unspecified(e) => write!(f, "unspecified compilation err: {}", e),
        }
    }
}

pub trait Compile {
    fn compile(self, input: ast::StmtNode) -> Result<Vec<u8>, CompileErr>;
}

#[derive(Default)]
pub struct Compiler {}

impl Compile for Compiler {
    /// Compile a string in the toy language into machine code.
    fn compile(mut self, input: ast::StmtNode) -> Result<Vec<u8>, CompileErr> {
        todo!()
    }
}

impl Compiler {
    fn translate(&mut self, input: ast::StmtNode) -> Result<(), String> {
        todo!()
    }
}

pub struct CodeGen;

impl CodeGen {
    fn codegen_expr(&mut self, expr: ast::ExprNode) -> String {
        use ast::{ExprNode, Primary};

        match expr {
            ExprNode::Primary(Primary::Uint8(ast::Uint8(ic))) => {
                use std::convert::TryFrom;
                let v: i64 = i64::try_from(ic).unwrap();
                todo!()
            }

            ExprNode::Addition(lhs, rhs) => {
                let lhs = self.codegen_expr(*lhs);
                let rhs = self.codegen_expr(*rhs);
                todo!()
            }

            ExprNode::Subtraction(lhs, rhs) => {
                let lhs = self.codegen_expr(*lhs);
                let rhs = self.codegen_expr(*rhs);
                todo!()
            }

            ExprNode::Multiplication(lhs, rhs) => {
                let lhs = self.codegen_expr(*lhs);
                let rhs = self.codegen_expr(*rhs);
                todo!()
            }

            ExprNode::Division(lhs, rhs) => {
                let lhs = self.codegen_expr(*lhs);
                let rhs = self.codegen_expr(*rhs);
                todo!()
            }
        }
    }
}
