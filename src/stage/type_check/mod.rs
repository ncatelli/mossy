//! The Type Pass module handles walking the raw parser ADT, performing
//! additional type checking and enrichment.

use super::CompilationStage;
use crate::ast::{self, type_compatible, Typed};

mod scopes;
use scopes::ScopeStack;

/// TypeAnalysis stores a scope stack for maintaining local variables.
#[derive(Default)]
pub struct TypeAnalysis {
    scopes: ScopeStack,
}

impl TypeAnalysis {
    /// Initializes a new TypeAnalysis pass with a global scope.
    pub fn new() -> Self {
        let mut scopes = ScopeStack::new();
        scopes.push_new_scope_mut();

        Self { scopes }
    }
}

impl CompilationStage<crate::parser::ast::Program, ast::TypedProgram, String> for TypeAnalysis {
    fn apply(&mut self, input: crate::parser::ast::Program) -> Result<ast::TypedProgram, String> {
        input
            .defs
            .into_iter()
            .map(|ast_node| self.apply(ast_node))
            .collect::<Result<Vec<ast::TypedFunctionDeclaration>, String>>()
            .map(ast::TypedProgram::new)
    }
}

impl
    CompilationStage<crate::parser::ast::FunctionDeclaration, ast::TypedFunctionDeclaration, String>
    for TypeAnalysis
{
    fn apply(
        &mut self,
        input: crate::parser::ast::FunctionDeclaration,
    ) -> Result<ast::TypedFunctionDeclaration, String> {
        let (id, block) = (input.id, input.block);
        self.scopes.define_mut(
            &id,
            ast::Type::Func {
                return_type: Box::new(ast::Type::Void),
            },
        );

        self.analyze_block(block)
            .map(|typed_block| ast::TypedFunctionDeclaration::new(id, typed_block))
    }
}

impl TypeAnalysis {
    fn analyze_block(
        &mut self,
        block: crate::parser::ast::CompoundStmts,
    ) -> Result<ast::TypedCompoundStmts, String> {
        self.scopes.push_new_scope_mut();
        let stmts = Vec::from(block);
        let mut typed_stmts = vec![];

        for stmt in stmts {
            let typed_stmt = self.analyze_statement(stmt)?;
            typed_stmts.push(typed_stmt)
        }

        self.scopes.pop_scope_mut();
        Ok(ast::TypedCompoundStmts::new(typed_stmts))
    }

    fn analyze_statement(
        &mut self,
        input: crate::parser::ast::StmtNode,
    ) -> Result<ast::TypedStmtNode, String> {
        match input {
            crate::parser::ast::StmtNode::Expression(expr) => self
                .analyze_expression(expr)
                .map(ast::TypedStmtNode::Expression),
            crate::parser::ast::StmtNode::Declaration(ty, id) => {
                self.scopes.define_mut(&id, ty.clone());
                Ok(ast::TypedStmtNode::Declaration(ty, id))
            }
            crate::parser::ast::StmtNode::Assignment(id, expr) => {
                let expr = self.analyze_expression(expr)?;
                self.scopes
                    .lookup(&id)
                    .map(|var_type| type_compatible(var_type, expr.r#type(), true))
                    .and_then(|type_compat| match type_compat {
                        ast::CompatibilityResult::Equivalent
                        | ast::CompatibilityResult::WidenTo(_) => Some(()),
                        ast::CompatibilityResult::Incompatible => None,
                    })
                    .map(|_| ast::TypedStmtNode::Assignment(id, expr))
                    .ok_or_else(|| "invalid type".to_string())
            }
            crate::parser::ast::StmtNode::If(cond, t_case, f_case) => {
                let typed_cond = self.analyze_expression(cond)?;
                let typed_t_case = self.analyze_block(t_case)?;
                let typed_f_case = if let Some(block) = f_case {
                    let res = self.analyze_block(block)?;
                    Some(res)
                } else {
                    None
                };

                Ok(ast::TypedStmtNode::If(
                    typed_cond,
                    typed_t_case,
                    typed_f_case,
                ))
            }
            crate::parser::ast::StmtNode::While(cond, block) => {
                let typed_cond = self.analyze_expression(cond)?;
                let typed_block = self.analyze_block(block)?;

                Ok(ast::TypedStmtNode::While(typed_cond, typed_block))
            }
            crate::parser::ast::StmtNode::For(preop, cond, postop, block) => {
                let typed_cond = self.analyze_expression(cond)?;
                let typed_preop = self.analyze_statement(*preop)?;
                let typed_postop = self.analyze_statement(*postop)?;
                let typed_block = self.analyze_block(block)?;

                Ok(ast::TypedStmtNode::For(
                    Box::new(typed_preop),
                    typed_cond,
                    Box::new(typed_postop),
                    typed_block,
                ))
            }
        }
    }

    fn analyze_expression(
        &self,
        expr: crate::parser::ast::ExprNode,
    ) -> Result<ast::TypedExprNode, String> {
        use crate::parser::ast::ExprNode;
        use crate::parser::ast::Primary;

        use crate::ast::Signed;

        match expr {
            ExprNode::Primary(Primary::Integer {
                sign: Signed::Unsigned,
                width,
                value,
            }) => {
                let sign = Signed::Unsigned;

                Ok(ast::TypedExprNode::Primary(
                    ast::Type::Integer(sign, width),
                    crate::ast::Primary::Integer { sign, width, value },
                ))
            }
            ExprNode::Primary(Primary::Integer {
                sign: Signed::Signed,
                width: _,
                value: _,
            }) => Err("unimplemented: signed integers".to_string()),
            ExprNode::Primary(Primary::Identifier(identifier)) => self
                .scopes
                .lookup(&identifier)
                .map(|r#type| {
                    ast::TypedExprNode::Primary(
                        r#type.clone(),
                        ast::Primary::Identifier(r#type, identifier),
                    )
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Equal(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::Equal(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::NotEqual(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::NotEqual(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid_type".to_string()),
            ExprNode::LessEqual(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::LessEqual(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::LessThan(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::LessThan(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::GreaterEqual(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::GreaterEqual(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::GreaterThan(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::GreaterThan(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Addition(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::Addition(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Subtraction(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::Subtraction(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),

            ExprNode::Division(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::Division(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Multiplication(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::Multiplication(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
        }
    }

    fn analyze_binary_expr(
        &self,
        lhs: crate::parser::ast::ExprNode,
        rhs: crate::parser::ast::ExprNode,
    ) -> Option<(ast::Type, ast::TypedExprNode, ast::TypedExprNode)> {
        let lhs = self.analyze_expression(lhs).unwrap();
        let rhs = self.analyze_expression(rhs).unwrap();

        match type_compatible(lhs.r#type(), rhs.r#type(), false) {
            ast::CompatibilityResult::Equivalent => Some((lhs.r#type(), lhs, rhs)),
            ast::CompatibilityResult::WidenTo(t) => Some((t, lhs, rhs)),
            ast::CompatibilityResult::Incompatible => None,
        }
    }
}
