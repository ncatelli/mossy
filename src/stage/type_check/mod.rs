//! The Type Pass module handles walking the raw parser ADT, performing
//! additional type checking and enrichment.

use super::CompilationStage;
use crate::stage::ast::{self, FuncProto, TypeCompatibility, Typed};

mod scopes;
use scopes::ScopeStack;

/// TypeAnalysis stores a scope stack for maintaining local variables.
#[derive(Default)]
pub struct TypeAnalysis {
    in_func: Option<(String, ast::FuncProto)>,
    scopes: ScopeStack,
}

impl TypeAnalysis {
    /// Initializes a new TypeAnalysis pass with a global scope.
    pub fn new() -> Self {
        let mut scopes = ScopeStack::new();
        scopes.push_new_scope_mut();

        Self {
            scopes,
            in_func: None,
        }
    }
}

impl CompilationStage<crate::parser::ast::Program, ast::TypedProgram, String> for TypeAnalysis {
    fn apply(&mut self, input: crate::parser::ast::Program) -> Result<ast::TypedProgram, String> {
        input
            .defs
            .into_iter()
            .map(|ast_node| self.apply(ast_node))
            .collect::<Result<Vec<ast::TypedGlobalDecls>, String>>()
            .map(ast::TypedProgram::new)
    }
}

impl CompilationStage<crate::parser::ast::GlobalDecls, ast::TypedGlobalDecls, String>
    for TypeAnalysis
{
    fn apply(
        &mut self,
        input: crate::parser::ast::GlobalDecls,
    ) -> Result<ast::TypedGlobalDecls, String> {
        use ast::Declaration;
        match input {
            crate::parser::ast::GlobalDecls::Func(fd) => {
                self.apply(fd).map(ast::TypedGlobalDecls::Func)
            }
            crate::parser::ast::GlobalDecls::Var(Declaration::Scalar(ty, ids)) => {
                for id in ids.iter() {
                    self.scopes.define_mut(id, ty.clone());
                }

                Ok(ast::TypedGlobalDecls::Var(ast::Declaration::Scalar(
                    ty, ids,
                )))
            }
            crate::parser::ast::GlobalDecls::Var(Declaration::Array { ty, id, size }) => {
                self.scopes.define_mut(&id, ty.pointer_to());

                Ok(ast::TypedGlobalDecls::Var(ast::Declaration::Array {
                    ty,
                    id,
                    size,
                }))
            }
        }
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

        let proto = FuncProto::new(Box::new(input.return_type), vec![]);
        self.scopes.define_mut(&id, ast::Type::Func(proto.clone()));

        self.analyze_function_body(id.clone(), proto, block)
            .map(|typed_block| ast::TypedFunctionDeclaration::new(id.clone(), typed_block))
    }
}

impl TypeAnalysis {
    fn analyze_function_body(
        &mut self,
        id: String,
        func_proto: FuncProto,
        block: crate::parser::ast::CompoundStmts,
    ) -> Result<ast::TypedCompoundStmts, String> {
        let old_body = self.in_func.replace((id, func_proto.clone()));
        self.scopes.push_new_scope_mut();

        let stmts = Vec::from(block);
        let mut typed_stmts = vec![];

        for stmt in stmts {
            let typed_stmt = self.analyze_statement(stmt)?;
            typed_stmts.push(typed_stmt)
        }

        let expected_ret_type = func_proto.return_type.as_ref();
        typed_stmts
            .last()
            .and_then(|last_stmt| match last_stmt {
                ast::TypedStmtNode::Return(rt, _, _) if expected_ret_type == rt => Some(rt),
                _ => None,
            })
            .ok_or_else(|| "invalid return type".to_string())?;

        // reset scope
        self.scopes.pop_scope_mut();
        self.in_func = old_body;

        Ok(ast::TypedCompoundStmts::new(typed_stmts))
    }

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
            crate::parser::ast::StmtNode::Declaration(ast::Declaration::Scalar(ty, ids)) => {
                for id in ids.iter() {
                    self.scopes.define_mut(id, ty.clone());
                }

                Ok(ast::TypedStmtNode::Declaration(ast::Declaration::Scalar(
                    ty, ids,
                )))
            }
            crate::parser::ast::StmtNode::Declaration(ast::Declaration::Array { ty, id, size }) => {
                self.scopes.define_mut(&id, ty.clone());

                Ok(ast::TypedStmtNode::Declaration(ast::Declaration::Array {
                    ty,
                    id,
                    size,
                }))
            }
            crate::parser::ast::StmtNode::Return(Some(rt_expr)) => {
                if let Some((id, proto)) = self.in_func.as_ref() {
                    let typed_expr = self.analyze_expression(rt_expr)?;
                    let expr_t = typed_expr.r#type();

                    let rt_type = match proto.return_type.as_ref().type_compatible(&expr_t, true) {
                        ast::CompatibilityResult::Equivalent => {
                            Ok(proto.return_type.as_ref().clone())
                        }
                        ast::CompatibilityResult::WidenTo(new_type) => Ok(new_type),
                        ast::CompatibilityResult::Incompatible => Err(format!(
                            "function type and return type are incompatible: {:?}",
                            proto.return_type.as_ref()
                        )),
                        ast::CompatibilityResult::Scale(_) => todo!(),
                    }?;

                    Ok(ast::TypedStmtNode::Return(
                        rt_type,
                        id.to_owned(),
                        Some(typed_expr),
                    ))
                } else {
                    Err("invalid use of return: not in function".to_string())
                }
            }
            crate::parser::ast::StmtNode::Return(None) => {
                if let Some((id, _)) = self.in_func.as_ref() {
                    Ok(ast::TypedStmtNode::Return(
                        ast::Type::Void,
                        id.to_owned(),
                        None,
                    ))
                } else {
                    Err("invalid use of return: not in function".to_string())
                }
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

        use ast::Signed;

        match expr {
            ExprNode::Primary(Primary::Integer {
                sign: Signed::Unsigned,
                width,
                value,
            }) => Ok(ast::TypedExprNode::Primary(
                ast::Type::Integer(Signed::Unsigned, width),
                ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width,
                    value,
                },
            )),
            ExprNode::Primary(Primary::Integer {
                sign: Signed::Signed,
                ..
            }) => Err("unimplemented: signed integers".to_string()),
            ExprNode::Primary(Primary::Identifier(identifier)) => self
                .scopes
                .lookup(&identifier)
                .map(|dm| {
                    ast::TypedExprNode::Primary(
                        dm.r#type.clone(),
                        ast::Primary::Identifier(dm.r#type, identifier),
                    )
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Primary(Primary::Str(_)) => todo!(),

            ExprNode::Grouping(expr) => self
                .analyze_expression(*expr)
                .map(|ty_expr| (ty_expr.r#type(), ty_expr))
                .map(|(ty, expr)| ast::TypedExprNode::Grouping(ty, Box::new(expr))),

            ExprNode::FunctionCall(identifier, args) => {
                let args = args.map(|arg| self.analyze_expression(*arg).unwrap());

                self.scopes
                    .lookup(&identifier)
                    .ok_or_else(|| format!("undefined_function: {}", &identifier))
                    .and_then(|dm| match dm.r#type {
                        ast::Type::Func(FuncProto {
                            return_type,
                            args: func_args,
                        }) if args.is_none() && func_args.is_empty() => {
                            Ok(ast::TypedExprNode::FunctionCall(
                                *return_type,
                                identifier,
                                args.map(Box::new),
                            ))
                        }
                        _ => Err(format!(
                            "type mismatch, cannot call non-function type: {:?}",
                            &dm.r#type
                        )),
                    })
            }

            ExprNode::Assignment(lhs, rhs) => {
                use ast::{Primary, TypedExprNode};

                let rhs = self.analyze_expression(*rhs)?;
                let lhs = self.analyze_expression(*lhs)?;

                match lhs {
                    TypedExprNode::Primary(lhs_ty, Primary::Identifier(_, id)) => self
                        .scopes
                        .lookup(&id)
                        .map(|dm| dm.r#type.type_compatible(&rhs.r#type(), true))
                        .ok_or(format!("symbol {} undefined", &id))
                        .and_then(|type_compat| match type_compat {
                            ast::CompatibilityResult::Equivalent => Ok(lhs_ty),
                            ast::CompatibilityResult::WidenTo(ty) => Ok(ty),
                            ast::CompatibilityResult::Incompatible => {
                                Err(format!("invalid type in identifier lookup for ({}):\n\texpected: lhs({:?})\n\tgot: rhs({:?})", &id, lhs_ty, &rhs.r#type()))
                            }
                            ast::CompatibilityResult::Scale(t) => Ok(t),
                        })
                        .map(|ty| ast::TypedExprNode::IdentifierAssignment(ty, id, Box::new(rhs))),
                    TypedExprNode::Deref(ty, expr) => match ty.type_compatible(&rhs.r#type(), true)
                    {
                        ast::CompatibilityResult::Equivalent => Ok(ty),
                        ast::CompatibilityResult::WidenTo(ty) => Ok(ty),
                        ast::CompatibilityResult::Incompatible => {
                            Err(format!("invalid type: ({:?})", ty))
                        }
                        ast::CompatibilityResult::Scale(t) => Ok(t),
                    }
                    .map(|ty| ast::TypedExprNode::DerefAssignment(ty, expr, Box::new(rhs))),
                    // Fail on any other type
                    _ => Err(format!("invalid assignment type: ({:?})", lhs.r#type(),)),
                }
            }
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
            ExprNode::Multiplication(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::Multiplication(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Division(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::Division(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Modulo(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    ast::TypedExprNode::Modulo(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),

            ExprNode::Ref(identifier) => self
                .scopes
                .lookup(&identifier)
                .map(|dm| ast::TypedExprNode::Ref(dm.r#type.pointer_to(), identifier))
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Deref(expr) => self
                .analyze_expression(*expr)
                .and_then(|ty_expr| {
                    ty_expr
                        .r#type()
                        .value_at()
                        .ok_or_else(|| "type is not a reference".to_string())
                        .map(|ty| (ty, ty_expr))
                })
                .map(|(ty, expr)| ast::TypedExprNode::Deref(ty, Box::new(expr))),
            ExprNode::Index(identifier, index) => {
                let ptr_width =
                    ast::Type::Integer(ast::Signed::Unsigned, ast::IntegerWidth::SixtyFour);

                let index_expr = self.analyze_expression(*index)?;
                let index_expr_ty = &index_expr.r#type();

                let index_expr = match ptr_width.type_compatible(&index_expr.r#type(), true) {
                    ast::CompatibilityResult::Equivalent => Some(index_expr),
                    ast::CompatibilityResult::WidenTo(ty) => {
                        Some(ast::TypedExprNode::Grouping(ty, Box::new(index_expr)))
                    }
                    ast::CompatibilityResult::Scale(_) | ast::CompatibilityResult::Incompatible => {
                        None
                    }
                }
                .ok_or_else(|| {
                    format!(
                        "array index cannot be widened to pointer width: {:?}",
                        &index_expr_ty
                    )
                })?;

                self.scopes
                    .lookup(&identifier)
                    // validate that the reference is a pointer type
                    .and_then(|reference| {
                        reference
                            .r#type
                            .value_at()
                            .map(|ptr_to_ty| (reference.r#type.clone(), ptr_to_ty))
                    })
                    .map(|(ref_ty, scale_by_ty)| {
                        (
                            ref_ty,
                            ast::TypedExprNode::ScaleBy(scale_by_ty, Box::new(index_expr)),
                        )
                    })
                    .map(|(ref_ty, scale)| {
                        // recast to a pointer as pulled from the above reference
                        ast::TypedExprNode::Addition(
                            ref_ty.clone(),
                            Box::new(ast::TypedExprNode::Ref(ref_ty, identifier.clone())),
                            Box::new(scale),
                        )
                    })
                    .and_then(|reference| {
                        reference
                            .r#type()
                            .value_at()
                            .map(|points_to_ty| (points_to_ty, reference))
                    })
                    .map(|(ref_points_to_ty, reference)| {
                        ast::TypedExprNode::Deref(ref_points_to_ty, Box::new(reference))
                    })
                    .ok_or_else(|| "invalid type".to_string())
            }
        }
    }

    fn analyze_binary_expr(
        &self,
        lhs: crate::parser::ast::ExprNode,
        rhs: crate::parser::ast::ExprNode,
    ) -> Option<(ast::Type, ast::TypedExprNode, ast::TypedExprNode)> {
        let lhs = self.analyze_expression(lhs).unwrap();
        let rhs = self.analyze_expression(rhs).unwrap();

        match lhs.r#type().type_compatible(&rhs.r#type(), false) {
            ast::CompatibilityResult::Equivalent => Some((lhs.r#type(), lhs, rhs)),
            ast::CompatibilityResult::WidenTo(ty) => Some((ty, lhs, rhs)),
            ast::CompatibilityResult::Incompatible => None,
            ast::CompatibilityResult::Scale(ty) => Some((
                ty.clone(),
                lhs,
                ast::TypedExprNode::ScaleBy(ty, Box::new(rhs)),
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::ast;
    use crate::stage::{
        self,
        ast::{IntegerWidth, Signed, Type, TypedExprNode},
    };

    #[test]
    fn test_grouping_assigns_correct_type() {
        let analyzer = super::TypeAnalysis::default();
        let pre_typed_ast =
            ast::ExprNode::Grouping(Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::Eight,
                value: 1,
            })));

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::Grouping(
            Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
            Box::new(TypedExprNode::Primary(
                Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                stage::ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: 1,
                },
            )),
        );

        assert_eq!(Ok(expected), typed_ast);

        // Preserves complex order

        let pre_typed_ast = ast::ExprNode::Grouping(Box::new(ast::ExprNode::Multiplication(
            Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::Eight,
                value: 2,
            })),
            Box::new(ast::ExprNode::Addition(
                Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: 3,
                })),
                Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: 4,
                })),
            )),
        )));

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::Grouping(
            Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
            Box::new(TypedExprNode::Multiplication(
                Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                Box::new(TypedExprNode::Primary(
                    Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                    stage::ast::Primary::Integer {
                        sign: Signed::Unsigned,
                        width: IntegerWidth::Eight,
                        value: 2,
                    },
                )),
                Box::new(TypedExprNode::Addition(
                    Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                    Box::new(TypedExprNode::Primary(
                        Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                        stage::ast::Primary::Integer {
                            sign: Signed::Unsigned,
                            width: IntegerWidth::Eight,
                            value: 3,
                        },
                    )),
                    Box::new(TypedExprNode::Primary(
                        Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                        stage::ast::Primary::Integer {
                            sign: Signed::Unsigned,
                            width: IntegerWidth::Eight,
                            value: 4,
                        },
                    )),
                )),
            )),
        );

        assert_eq!(Ok(expected), typed_ast);
    }
}
