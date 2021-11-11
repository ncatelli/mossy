use crate::ast::typing::{type_compatible, Typed};
use crate::ast::{self, ExprNode};
use crate::codegen::TreePass;
use crate::env::ScopeStack;
use crate::parser::identifier;

pub struct TypeAnalysis {
    scopes: ScopeStack,
}

impl TypeAnalysis {
    pub fn new() -> Self {
        Self {
            scopes: ScopeStack::new(),
        }
    }
}

impl TreePass<ast::FunctionDeclaration, ast::typing::TypedFunctionDeclaration> for TypeAnalysis {
    type Error = String;

    fn analyze(
        &mut self,
        input: ast::FunctionDeclaration,
    ) -> Result<ast::typing::TypedFunctionDeclaration, Self::Error> {
        let (id, block) = (input.id, input.block);
        self.scopes.define_mut(&id, ast::typing::Type::Void);

        self.analyze_block(block)
            .map(|typed_block| ast::typing::TypedFunctionDeclaration::new(id, typed_block))
    }
}

impl TypeAnalysis {
    fn analyze_block(
        &mut self,
        block: ast::CompoundStmts,
    ) -> Result<ast::typing::TypedCompoundStmts, String> {
        self.scopes.push_new_scope_mut();
        let stmts = Vec::from(block);
        let mut typed_stmts = vec![];

        for stmt in stmts {
            let typed_stmt = self.analyze_statement(stmt)?;
            typed_stmts.push(typed_stmt)
        }

        self.scopes.pop_scope_mut();
        Ok(ast::typing::TypedCompoundStmts::new(typed_stmts))
    }

    fn analyze_statement(
        &mut self,
        input: ast::StmtNode,
    ) -> Result<ast::typing::TypedStmtNode, String> {
        match input {
            ast::StmtNode::Expression(expr) => self
                .analyze_expression(expr)
                .map(ast::typing::TypedStmtNode::Expression),
            ast::StmtNode::Declaration(ty, id) => {
                self.scopes.define_mut(&id, ty);
                Ok(ast::typing::TypedStmtNode::Declaration(ty, id))
            }
            ast::StmtNode::Assignment(id, expr) => {
                let expr = self.analyze_expression(expr)?;
                self.scopes
                    .lookup(&id)
                    .map(|var_type| type_compatible(var_type, expr.r#type(), true))
                    .and_then(|type_compat| match type_compat {
                        ast::typing::CompatibilityResult::Equivalent
                        | ast::typing::CompatibilityResult::WidenTo(_) => Some(()),
                        ast::typing::CompatibilityResult::Incompatible => None,
                    })
                    .map(|_| ast::typing::TypedStmtNode::Assignment(id, expr))
                    .ok_or_else(|| "invalid type".to_string())
            }
            ast::StmtNode::If(cond, t_case, f_case) => {
                let typed_cond = self.analyze_expression(cond)?;
                let typed_t_case = self.analyze_block(t_case)?;
                let typed_f_case = if let Some(block) = f_case {
                    let res = self.analyze_block(block)?;
                    Some(res)
                } else {
                    None
                };

                Ok(ast::typing::TypedStmtNode::If(
                    typed_cond,
                    typed_t_case,
                    typed_f_case,
                ))
            }
            ast::StmtNode::While(cond, block) => {
                let typed_cond = self.analyze_expression(cond)?;
                let typed_block = self.analyze_block(block)?;

                Ok(ast::typing::TypedStmtNode::While(typed_cond, typed_block))
            }
            ast::StmtNode::For(preop, cond, postop, block) => {
                let typed_cond = self.analyze_expression(cond)?;
                let typed_preop = self.analyze_statement(*preop)?;
                let typed_postop = self.analyze_statement(*postop)?;
                let typed_block = self.analyze_block(block)?;

                Ok(ast::typing::TypedStmtNode::For(
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
        expr: ast::ExprNode,
    ) -> Result<ast::typing::TypedExprNode, String> {
        use ast::Primary;

        match expr {
            ExprNode::Primary(Primary::Uint8(ast::Uint8(uc))) => {
                Ok(ast::typing::TypedExprNode::Primary(
                    ast::typing::Type::Uint8,
                    ast::typing::Primary::Uint8(ast::typing::Uint8(uc)),
                ))
            }
            ExprNode::Primary(Primary::Identifier(identifier)) => self
                .scopes
                .lookup(&identifier)
                .map(|r#type| {
                    ast::typing::TypedExprNode::Primary(
                        r#type,
                        ast::typing::Primary::Identifier(r#type, identifier),
                    )
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Equal(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::typing::TypedExprNode::Equal(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::NotEqual(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::typing::TypedExprNode::NotEqual(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid_type".to_string()),
            ExprNode::LessEqual(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::typing::TypedExprNode::LessEqual(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::LessThan(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::typing::TypedExprNode::LessThan(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::GreaterEqual(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::typing::TypedExprNode::GreaterEqual(
                        expr_type,
                        Box::new(lhs),
                        Box::new(rhs),
                    )
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::GreaterThan(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::typing::TypedExprNode::GreaterThan(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Addition(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::typing::TypedExprNode::Addition(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Subtraction(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::typing::TypedExprNode::Subtraction(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),

            ExprNode::Division(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::typing::TypedExprNode::Division(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Multiplication(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::typing::TypedExprNode::Multiplication(
                        expr_type,
                        Box::new(lhs),
                        Box::new(rhs),
                    )
                })
                .ok_or_else(|| "invalid type".to_string()),
        }
    }

    fn analyze_binary_expr(
        &self,
        lhs: ExprNode,
        rhs: ExprNode,
    ) -> Option<(
        ast::typing::Type,
        ast::typing::TypedExprNode,
        ast::typing::TypedExprNode,
    )> {
        use ast::typing::type_compatible;

        let lhs = self.analyze_expression(lhs).unwrap();
        let rhs = self.analyze_expression(rhs).unwrap();

        match type_compatible(lhs.r#type(), rhs.r#type(), false) {
            ast::typing::CompatibilityResult::Equivalent => Some((lhs.r#type(), lhs, rhs)),
            ast::typing::CompatibilityResult::WidenTo(t) => Some((t, lhs, rhs)),
            ast::typing::CompatibilityResult::Incompatible => None,
        }
    }
}
