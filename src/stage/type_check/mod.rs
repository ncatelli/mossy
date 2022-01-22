//! The Type Pass module handles walking the raw parser ADT, performing
//! additional type checking and enrichment.

use super::CompilationStage;
use crate::stage::ast::{ FuncProto, Typed};

mod ast;

mod scopes;
use scopes::ScopeStack;

#[derive(Clone, Copy, PartialEq, Eq)]
struct Integer {
    signed: crate::stage::ast::Signed,
    width: crate::stage::ast::IntegerWidth,
}

impl Integer {
    fn new(signed: crate::stage::ast::Signed, width: crate::stage::ast::IntegerWidth) -> Self {
        Self { signed, width }
    }
}

impl std::convert::TryFrom<usize> for Integer {
    type Error = String;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        use crate::stage::ast::{IntegerWidth, Signed};
        match value {
            0 => Ok(Integer::new(Signed::Signed, IntegerWidth::One)),
            1 => Ok(Integer::new(Signed::Unsigned, IntegerWidth::One)),
            2 => Ok(Integer::new(Signed::Signed, IntegerWidth::Eight)),
            3 => Ok(Integer::new(Signed::Unsigned, IntegerWidth::Eight)),
            4 => Ok(Integer::new(Signed::Signed, IntegerWidth::Sixteen)),
            5 => Ok(Integer::new(Signed::Unsigned, IntegerWidth::Sixteen)),
            6 => Ok(Integer::new(Signed::Signed, IntegerWidth::ThirtyTwo)),
            7 => Ok(Integer::new(Signed::Unsigned, IntegerWidth::ThirtyTwo)),
            8 => Ok(Integer::new(Signed::Signed, IntegerWidth::SixtyFour)),
            9 => Ok(Integer::new(Signed::Unsigned, IntegerWidth::SixtyFour)),
            _ => Err(format!("rank {} outside of accepted range", value)),
        }
    }
}

trait Ranking {
    type Output;

    fn rank(&self) -> Self::Output;
}

impl Ranking for crate::stage::ast::Signed {
    type Output = usize;

    fn rank(&self) -> Self::Output {
        match self {
            crate::stage::ast::Signed::Signed => 0,
            crate::stage::ast::Signed::Unsigned => 1,
        }
    }
}

impl Ranking for crate::stage::ast::IntegerWidth {
    type Output = usize;

    fn rank(&self) -> Self::Output {
        match self {
            crate::stage::ast::IntegerWidth::One => 0,
            crate::stage::ast::IntegerWidth::Eight => 2,
            crate::stage::ast::IntegerWidth::Sixteen => 4,
            crate::stage::ast::IntegerWidth::ThirtyTwo => 6,
            crate::stage::ast::IntegerWidth::SixtyFour => 8,
        }
    }
}

impl Ranking for Integer {
    type Output = usize;

    fn rank(&self) -> Self::Output {
        let (sign, width) = (&self.signed, &self.width);
        sign.rank() + width.rank()
    }
}

const fn is_even(n: usize) -> bool {
    n % 2 == 0
}

fn calculate_satisfying_integer_size_from_rank(lhs: usize, rhs: usize) -> usize {
    let max = core::cmp::max(lhs, rhs);
    let min = core::cmp::min(lhs, rhs);

    // promote to next largest signed integer
    if !is_even(max) && is_even(min) {
        max + 1
    } else {
        max
    }
}

enum CompatibilityResult {
    Equivalent,
    WidenTo(crate::stage::ast::Type),
    Scale(crate::stage::ast::Type),
    Incompatible,
}

/// A marker trait for defining the manner in which type compatibility is
/// asserted on an expression.
pub trait EvaluationFlow {}

/// An expressions type must be compatible with the left hand side's type.
struct LeftFlowing;

impl EvaluationFlow for LeftFlowing {}

/// An expressions type can be derived from the smallest type that encompasses
/// all values of the sub-expressions' types.
struct SmallestEncompassing;

impl EvaluationFlow for SmallestEncompassing {}

/// Defines a method for assessing if two types are compatible, either
/// explicitly or implicitly.
trait TypeCompatibility {
    type Output;
    type Lhs;
    type Rhs;

    fn type_compatible(&self, lhs: &Self::Lhs, rhs: &Self::Rhs) -> Self::Output;
}

impl TypeCompatibility for SmallestEncompassing {
    type Output = CompatibilityResult;
    type Lhs = crate::stage::ast::Type;
    type Rhs = crate::stage::ast::Type;

    fn type_compatible(&self, lhs: &Self::Lhs, rhs: &Self::Rhs) -> Self::Output {
        use crate::stage::ast::Type;

        match (lhs, rhs) {
            (lhs, rhs) if lhs == rhs => CompatibilityResult::Equivalent,
            (Type::Integer(l_sign, l_width), Type::Integer(r_sign, r_width)) => {
                let (lhs_rank, rhs_rank) = (
                    Integer::new(*l_sign, *l_width).rank(),
                    Integer::new(*r_sign, *r_width).rank(),
                );

                let adjusted_rank = calculate_satisfying_integer_size_from_rank(lhs_rank, rhs_rank);

                core::convert::TryFrom::try_from(adjusted_rank)
                    .map(|Integer { signed, width }| (signed, width))
                    .map(|(sign, width)| CompatibilityResult::WidenTo(Type::Integer(sign, width)))
                    .unwrap_or(CompatibilityResult::Incompatible)
            }
            (Type::Pointer(ty), Type::Integer(_, _)) => CompatibilityResult::Scale(*ty.clone()),
            _ => CompatibilityResult::Incompatible,
        }
    }
}

impl TypeCompatibility for LeftFlowing {
    type Output = CompatibilityResult;
    type Lhs = crate::stage::ast::Type;
    type Rhs = crate::stage::ast::Type;

    fn type_compatible(&self, lhs: &Self::Lhs, rhs: &Self::Rhs) -> Self::Output {
        use crate::stage::ast::Type;

        match (lhs, rhs) {
            (lhs, rhs) if lhs == rhs => CompatibilityResult::Equivalent,
            (Type::Integer(l_sign, l_width), Type::Integer(r_sign, r_width)) => {
                let (lhs_rank, rhs_rank) = (
                    Integer::new(*l_sign, *l_width).rank(),
                    Integer::new(*r_sign, *r_width).rank(),
                );

                if lhs_rank < rhs_rank {
                    CompatibilityResult::Incompatible
                } else {
                    SmallestEncompassing.type_compatible(lhs, rhs)
                }
            }
            (Type::Pointer(ty), Type::Integer(_, _)) => CompatibilityResult::Scale(*ty.clone()),
            _ => CompatibilityResult::Incompatible,
        }
    }
}

/// TypeAnalysis stores a scope stack for maintaining local variables.
pub struct TypeAnalysis {
    in_func: Option<(String, crate::stage::ast::FuncProto)>,
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

impl Default for TypeAnalysis {
    fn default() -> Self {
        let mut scopes = ScopeStack::new();
        scopes.push_new_scope_mut();

        Self {
            scopes,
            in_func: None,
        }
    }
}

impl CompilationStage<crate::parser::ast::CompilationUnit, crate::stage::ast::TypedProgram, String>
    for TypeAnalysis
{
    fn apply(
        &mut self,
        input: crate::parser::ast::CompilationUnit,
    ) -> Result<crate::stage::ast::TypedProgram, String> {
        input
            .defs
            .into_iter()
            .map(|ast_node| self.apply(ast_node))
            .collect::<Result<Vec<crate::stage::ast::TypedGlobalDecls>, String>>()
            .map(crate::stage::ast::TypedProgram::new)
    }
}

impl CompilationStage<crate::parser::ast::GlobalDecls, crate::stage::ast::TypedGlobalDecls, String>
    for TypeAnalysis
{
    fn apply(
        &mut self,
        input: crate::parser::ast::GlobalDecls,
    ) -> Result<crate::stage::ast::TypedGlobalDecls, String> {
        use crate::stage::ast::Declaration;
        match input {
            crate::parser::ast::GlobalDecls::Func(fd) => {
                self.apply(fd).map(crate::stage::ast::TypedGlobalDecls::Func)
            }
            crate::parser::ast::GlobalDecls::Var(Declaration::Scalar(ty, ids)) => {
                for id in ids.iter() {
                    self.scopes
                        .define_global_mut(id, ty.clone(), scopes::Kind::Basic);
                }

                Ok(crate::stage::ast::TypedGlobalDecls::Var(crate::stage::ast::Declaration::Scalar(
                    ty, ids,
                )))
            }
            crate::parser::ast::GlobalDecls::Var(Declaration::Array { ty, id, size }) => {
                self.scopes
                    .define_global_mut(&id, ty.pointer_to(), scopes::Kind::Array(size));

                Ok(crate::stage::ast::TypedGlobalDecls::Var(crate::stage::ast::Declaration::Array {
                    ty,
                    id,
                    size,
                }))
            }
        }
    }
}

impl
    CompilationStage<crate::parser::ast::FunctionDeclaration, crate::stage::ast::TypedFunctionDeclaration, String>
    for TypeAnalysis
{
    fn apply(
        &mut self,
        input: crate::parser::ast::FunctionDeclaration,
    ) -> Result<crate::stage::ast::TypedFunctionDeclaration, String> {
        let (id, block) = (input.id, input.block);

        let proto = FuncProto::new(Box::new(input.return_type), vec![]);
        self.scopes
            .define_global_mut(&id, crate::stage::ast::Type::Func(proto.clone()), scopes::Kind::Basic);

        self.analyze_function_body(id.clone(), proto, block).map(
            |(typed_block, local_variable_sized)| {
                crate::stage::ast::TypedFunctionDeclaration::new(id.clone(), typed_block, local_variable_sized)
            },
        )
    }
}

impl TypeAnalysis {
    fn analyze_function_body(
        &mut self,
        id: String,
        func_proto: FuncProto,
        block: crate::parser::ast::CompoundStmts,
    ) -> Result<(crate::stage::ast::TypedCompoundStmts, isize), String> {
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
                crate::stage::ast::TypedStmtNode::Return(rt, _, _) if expected_ret_type == rt => Some(rt),
                _ => None,
            })
            .ok_or_else(|| "invalid return type".to_string())?;

        let local_stack_offsets = self.scopes.local_offset();

        // reset scope
        self.scopes.pop_scope_mut();
        self.in_func = old_body;

        Ok((
            crate::stage::ast::TypedCompoundStmts::new(typed_stmts),
            local_stack_offsets,
        ))
    }

    fn analyze_block(
        &mut self,
        block: crate::parser::ast::CompoundStmts,
    ) -> Result<crate::stage::ast::TypedCompoundStmts, String> {
        self.scopes.push_new_scope_mut();
        let stmts = Vec::from(block);
        let mut typed_stmts = vec![];

        for stmt in stmts {
            let typed_stmt = self.analyze_statement(stmt)?;
            typed_stmts.push(typed_stmt)
        }

        self.scopes.pop_scope_mut();
        Ok(crate::stage::ast::TypedCompoundStmts::new(typed_stmts))
    }

    fn analyze_statement(
        &mut self,
        input: crate::parser::ast::StmtNode,
    ) -> Result<crate::stage::ast::TypedStmtNode, String> {
        match input {
            crate::parser::ast::StmtNode::Expression(expr) => self
                .analyze_expression(expr)
                .map(crate::stage::ast::TypedStmtNode::Expression),
            crate::parser::ast::StmtNode::Declaration(crate::stage::ast::Declaration::Scalar(ty, ids)) => {
                let local_offsets = ids
                    .iter()
                    .map(|id| {
                        self.scopes
                            .define_local_mut(id, ty.clone(), scopes::Kind::Basic)
                    })
                    .collect();

                Ok(crate::stage::ast::TypedStmtNode::LocalDeclaration(
                    crate::stage::ast::Declaration::Scalar(ty, ids),
                    local_offsets,
                ))
            }
            crate::parser::ast::StmtNode::Declaration(crate::stage::ast::Declaration::Array { ty, id, size }) => {
                let local_offset =
                    self.scopes
                        .define_local_mut(&id, ty.pointer_to(), scopes::Kind::Array(size));

                Ok(crate::stage::ast::TypedStmtNode::LocalDeclaration(
                    crate::stage::ast::Declaration::Array { ty, id, size },
                    vec![local_offset],
                ))
            }
            crate::parser::ast::StmtNode::Return(Some(rt_expr)) => {
                if let Some((id, proto)) = self.in_func.as_ref() {
                    let typed_expr = self.analyze_expression(rt_expr)?;
                    let expr_t = typed_expr.r#type();
                    let return_type_compatibility =
                        LeftFlowing.type_compatible(proto.return_type.as_ref(), &expr_t);

                    let rt_type = match return_type_compatibility {
                        CompatibilityResult::Equivalent => Ok(proto.return_type.as_ref().clone()),
                        CompatibilityResult::WidenTo(new_type) => Ok(new_type),
                        CompatibilityResult::Incompatible => Err(format!(
                            "function type and return type are incompatible: {:?}",
                            proto.return_type.as_ref()
                        )),
                        CompatibilityResult::Scale(_) => todo!(),
                    }?;

                    Ok(crate::stage::ast::TypedStmtNode::Return(
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
                    Ok(crate::stage::ast::TypedStmtNode::Return(
                        crate::stage::ast::Type::Void,
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

                Ok(crate::stage::ast::TypedStmtNode::If(
                    typed_cond,
                    typed_t_case,
                    typed_f_case,
                ))
            }
            crate::parser::ast::StmtNode::While(cond, block) => {
                let typed_cond = self.analyze_expression(cond)?;
                let typed_block = self.analyze_block(block)?;

                Ok(crate::stage::ast::TypedStmtNode::While(typed_cond, typed_block))
            }
            crate::parser::ast::StmtNode::For(preop, cond, postop, block) => {
                let typed_cond = self.analyze_expression(cond)?;
                let typed_preop = self.analyze_statement(*preop)?;
                let typed_postop = self.analyze_statement(*postop)?;
                let typed_block = self.analyze_block(block)?;

                Ok(crate::stage::ast::TypedStmtNode::For(
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
    ) -> Result<crate::stage::ast::TypedExprNode, String> {
        use crate::parser::ast::ExprNode;
        use crate::parser::ast::Primary;

        match expr {
            ExprNode::Primary(Primary::Integer { sign, width, value }) => {
                Ok(crate::stage::ast::TypedExprNode::Primary(
                    crate::stage::ast::Type::Integer(sign, width),
                    crate::stage::ast::Primary::Integer { sign, width, value },
                ))
            }
            ExprNode::Primary(Primary::Identifier(identifier)) => self
                .scopes
                .lookup(&identifier)
                .ok_or_else(|| format!("identifier ({}) undefined", &identifier))
                .map(|dm| match (dm.is_array(), dm.is_local) {
                    (true, None) => crate::stage::ast::TypedExprNode::Ref(
                        dm.r#type,
                        crate::stage::ast::IdentifierLocality::Global(identifier),
                    ),
                    (false, None) => crate::stage::ast::TypedExprNode::Primary(
                        dm.r#type.clone(),
                        crate::stage::ast::Primary::Identifier(
                            dm.r#type,
                            crate::stage::ast::IdentifierLocality::Global(identifier),
                        ),
                    ),
                    (true, Some(offset)) => {
                        crate::stage::ast::TypedExprNode::Ref(dm.r#type, crate::stage::ast::IdentifierLocality::Local(offset))
                    }
                    (false, Some(offset)) => crate::stage::ast::TypedExprNode::Primary(
                        dm.r#type.clone(),
                        crate::stage::ast::Primary::Identifier(dm.r#type, crate::stage::ast::IdentifierLocality::Local(offset)),
                    ),
                }),
            ExprNode::Primary(Primary::Str(elems)) => Ok(crate::stage::ast::TypedExprNode::Primary(
                generate_type_specifier!(ptr => generate_type_specifier!(char)),
                crate::stage::ast::Primary::Str(elems),
            )),

            ExprNode::Grouping(expr) => self
                .analyze_expression(*expr)
                .map(|ty_expr| (ty_expr.r#type(), ty_expr))
                .map(|(ty, expr)| crate::stage::ast::TypedExprNode::Grouping(ty, Box::new(expr))),

            ExprNode::FunctionCall(identifier, args) => {
                let args = args.map(|arg| self.analyze_expression(*arg).unwrap());

                self.scopes
                    .lookup(&identifier)
                    .ok_or_else(|| format!("undefined_function: {}", &identifier))
                    .and_then(|dm| match dm.r#type {
                        crate::stage::ast::Type::Func(FuncProto {
                            return_type,
                            args: func_args,
                        }) if args.is_none() && func_args.is_empty() => {
                            Ok(crate::stage::ast::TypedExprNode::FunctionCall(
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
                use crate::stage::ast::{Primary, TypedExprNode};

                let rhs = self.analyze_expression(*rhs)?;
                let lhs = self.analyze_expression(*lhs)?;

                match lhs {
                    TypedExprNode::Primary(lhs_ty, Primary::Identifier(_, crate::stage::ast::IdentifierLocality::Global(id))) => self
                        .scopes
                        .lookup(&id)
                        .map(|dm| LeftFlowing.type_compatible(&dm.r#type, &rhs.r#type()))
                        .ok_or(format!("symbol {} undefined", &id))
                        .and_then(|type_compat| match type_compat {
                            CompatibilityResult::Equivalent => Ok(lhs_ty),
                            CompatibilityResult::WidenTo(ty) => Ok(ty),
                            CompatibilityResult::Incompatible => {
                                Err(format!("invalid type in identifier lookup for ({}):\n\texpected: lhs({:?})\n\tgot: rhs({:?})", &id, lhs_ty, &rhs.r#type()))
                            }
                            CompatibilityResult::Scale(t) => Ok(t),
                        })
                        .map(|ty| crate::stage::ast::TypedExprNode::IdentifierAssignment(ty, crate::stage::ast::IdentifierLocality::Global(id), Box::new(rhs))),
                    TypedExprNode::Primary(lhs_ty, Primary::Identifier(ty, crate::stage::ast::IdentifierLocality::Local(offset))) =>{ 
                        let type_compat = LeftFlowing.type_compatible(&ty, &rhs.r#type());
                         match type_compat {
                            CompatibilityResult::Equivalent => Ok(lhs_ty),
                            CompatibilityResult::WidenTo(ty) => Ok(ty),
                            CompatibilityResult::Incompatible => {
                                Err(format!("invalid type in identifier:\n\texpected: lhs({:?})\n\tgot: rhs({:?})", lhs_ty, &rhs.r#type()))
                            }
                            CompatibilityResult::Scale(t) => Ok(t),
                        }
                        .map(|ty| crate::stage::ast::TypedExprNode::IdentifierAssignment(ty, crate::stage::ast::IdentifierLocality::Local(offset), Box::new(rhs)))
                    }
                    TypedExprNode::Deref(ty, expr) => match LeftFlowing.type_compatible(&ty, &rhs.r#type())
                
                    {
                        CompatibilityResult::Equivalent => Ok(ty),
                        CompatibilityResult::WidenTo(ty) => Ok(ty),
                        CompatibilityResult::Incompatible => {
                            Err(format!("invalid type: ({:?})", ty))
                        }
                        CompatibilityResult::Scale(t) => Ok(t),
                    }
                    .map(|ty| crate::stage::ast::TypedExprNode::DerefAssignment(ty, expr, Box::new(rhs))),
                    // Fail on any other type
                    _ => Err(format!("invalid assignment type: ({:?})", lhs.r#type())),
                }
            }

            ExprNode::LogOr(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(_, lhs, rhs)| {
                    let ty = crate::stage::ast::Type::Integer(crate::stage::ast::Signed::Unsigned, crate::stage::ast::IntegerWidth::One);
                    crate::stage::ast::TypedExprNode::LogOr(ty, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "incompatible types for logical or comparison".to_string()),
            ExprNode::LogAnd(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(_, lhs, rhs)| {
                    let ty = crate::stage::ast::Type::Integer(crate::stage::ast::Signed::Unsigned, crate::stage::ast::IntegerWidth::One);
                    crate::stage::ast::TypedExprNode::LogAnd(ty, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "incompatible types for logical and comparison".to_string()),

            ExprNode::BitOr(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(_, lhs, rhs)| {
                    let ty = crate::stage::ast::Type::Integer(crate::stage::ast::Signed::Unsigned, crate::stage::ast::IntegerWidth::One);
                    crate::stage::ast::TypedExprNode::BitOr(ty, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "incompatible types for bitwise or operation".to_string()),
            ExprNode::BitXor(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(_, lhs, rhs)| {
                    let ty = crate::stage::ast::Type::Integer(crate::stage::ast::Signed::Unsigned, crate::stage::ast::IntegerWidth::One);
                    crate::stage::ast::TypedExprNode::BitXor(ty, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "incompatible types for bitwise xor operation".to_string()),
            ExprNode::BitAnd(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(_, lhs, rhs)| {
                    let ty = crate::stage::ast::Type::Integer(crate::stage::ast::Signed::Unsigned, crate::stage::ast::IntegerWidth::One);
                    crate::stage::ast::TypedExprNode::BitAnd(ty, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "incompatible types for bitwise and operation".to_string()),

            ExprNode::Equal(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::Equal(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::NotEqual(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::NotEqual(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid_type".to_string()),
            ExprNode::LessEqual(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::LessEqual(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::LessThan(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::LessThan(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::GreaterEqual(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::GreaterEqual(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::GreaterThan(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::GreaterThan(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),

            ExprNode::BitShiftLeft(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .and_then(|(expr_type, lhs, rhs)| {
                    match LeftFlowing.type_compatible(&generate_type_specifier!(u8), &rhs.r#type())
                    {
                        CompatibilityResult::Scale(_) | CompatibilityResult::Incompatible => None,
                        CompatibilityResult::Equivalent | CompatibilityResult::WidenTo(_) => {
                            Some((expr_type, lhs, rhs))
                        }
                    }
                })
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::BitShiftLeft(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "incompatible operands to left shift operation".to_string()),

            ExprNode::BitShiftRight(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .and_then(|(expr_type, lhs, rhs)| {
                    match LeftFlowing.type_compatible(&generate_type_specifier!(u8), &rhs.r#type())
                    {
                        CompatibilityResult::Scale(_) | CompatibilityResult::Incompatible => None,
                        CompatibilityResult::Equivalent | CompatibilityResult::WidenTo(_) => {
                            Some((expr_type, lhs, rhs))
                        }
                    }
                })
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::BitShiftRight(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "incompatible operands to right shift operation".to_string()),

            ExprNode::Addition(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::Addition(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Subtraction(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::Subtraction(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Multiplication(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::Multiplication(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Division(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::Division(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),
            ExprNode::Modulo(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(expr_type, lhs, rhs)| {
                    crate::stage::ast::TypedExprNode::Modulo(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "invalid type".to_string()),

            ExprNode::LogicalNot(expr) => self
                .analyze_expression(*expr)
                .map(|expr| (expr.r#type(), expr))
                .map(|(expr_type, expr)| crate::stage::ast::TypedExprNode::LogicalNot(expr_type, Box::new(expr))),
            ExprNode::Negate(expr) => self
                .analyze_expression(*expr)
                .map(|expr| (expr.r#type(), expr))
                .and_then(|(expr_type, expr)| {
                    match LeftFlowing.type_compatible(&expr_type, &generate_type_specifier!(i8)) {
                        CompatibilityResult::Equivalent => Some(expr_type),
                        CompatibilityResult::WidenTo(ty) => Some(ty),
                        CompatibilityResult::Scale(_) | CompatibilityResult::Incompatible => None,
                    }
                    .ok_or_else(|| {
                        format!(
                            "negate operation expected iteger type: got {:?}",
                            expr.r#type()
                        )
                    })
                    .map(|ty| (ty, expr))
                })
                .map(|(expr_type, expr)| crate::stage::ast::TypedExprNode::Negate(expr_type, Box::new(expr))),
            ExprNode::Invert(expr) => self
                .analyze_expression(*expr)
                .map(|expr| (expr.r#type(), expr))
                .map(|(expr_type, expr)| crate::stage::ast::TypedExprNode::Invert(expr_type, Box::new(expr))),

            ExprNode::PreIncrement(expr) => {
                self.analyze_inc_dec_expr(IncDecExpr::PreIncrement, *expr)
            }
            ExprNode::PreDecrement(expr) => {
                self.analyze_inc_dec_expr(IncDecExpr::PreDecrement, *expr)
            }
            ExprNode::PostIncrement(expr) => {
                self.analyze_inc_dec_expr(IncDecExpr::PostIncrement, *expr)
            }
            ExprNode::PostDecrement(expr) => {
                self.analyze_inc_dec_expr(IncDecExpr::PostDecrement, *expr)
            }
            ExprNode::Ref(identifier) => self
                .scopes
                .lookup(&identifier)
                .map(|dm| match dm.is_local {
                    None => crate::stage::ast::TypedExprNode::Ref(
                        dm.r#type.pointer_to(),
                        crate::stage::ast::IdentifierLocality::Global(identifier),
                    ),
                    Some(offset) => crate::stage::ast::TypedExprNode::Ref(
                        dm.r#type.pointer_to(),
                        crate::stage::ast::IdentifierLocality::Local(offset),
                    ),
                })
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
                .map(|(ty, expr)| crate::stage::ast::TypedExprNode::Deref(ty, Box::new(expr))),
            ExprNode::Index(identifier, index) => {
                let ptr_width =
                    crate::stage::ast::Type::Integer(crate::stage::ast::Signed::Signed, crate::stage::ast::IntegerWidth::SixtyFour);

                let index_expr = self.analyze_expression(*index)?;
                let index_expr_ty = &index_expr.r#type();

                let index_expr =
                    match LeftFlowing.type_compatible(&ptr_width, &index_expr.r#type()) {
                        CompatibilityResult::Equivalent => Some(index_expr),
                        CompatibilityResult::WidenTo(ty) => {
                            Some(crate::stage::ast::TypedExprNode::Grouping(ty, Box::new(index_expr)))
                        }
                        CompatibilityResult::Scale(_) | CompatibilityResult::Incompatible => None,
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
                        reference.r#type.value_at().map(|value_of_ref| {
                            (
                                reference,
                                crate::stage::ast::TypedExprNode::ScaleBy(value_of_ref, Box::new(index_expr)),
                            )
                        })
                    })
                    .map(|(dm, scale)| {
                        let ref_ty = dm.r#type.clone();

                        let l_value_access = match (dm.is_array(), dm.is_local) {
                            (true, None) => Box::new(crate::stage::ast::TypedExprNode::Ref(
                                ref_ty.clone(),
                                crate::stage::ast::IdentifierLocality::Global(identifier.clone()),
                            )),
                            (false, None) => Box::new(crate::stage::ast::TypedExprNode::Primary(
                                ref_ty.clone(),
                                crate::stage::ast::Primary::Identifier(
                                    ref_ty.clone(),
                                    crate::stage::ast::IdentifierLocality::Global(identifier.clone()),
                                ),
                            )),
                            (true, Some(offset)) => Box::new(crate::stage::ast::TypedExprNode::Ref(
                                ref_ty.clone(),
                                crate::stage::ast::IdentifierLocality::Local(offset),
                            )),
                            (false, Some(offset)) => Box::new(crate::stage::ast::TypedExprNode::Primary(
                                ref_ty.clone(),
                                crate::stage::ast::Primary::Identifier(
                                    ref_ty.clone(),
                                    crate::stage::ast::IdentifierLocality::Local(offset),
                                ),
                            )),
                        };

                        // recast to a pointer as pulled from the above reference
                        if dm.is_local.is_none() {
                            crate::stage::ast::TypedExprNode::Addition(ref_ty, l_value_access, Box::new(scale))
                        } else {
                            crate::stage::ast::TypedExprNode::Subtraction(ref_ty, l_value_access, Box::new(scale))
                        }
                    })
                    .and_then(|reference| {
                        reference
                            .r#type()
                            .value_at()
                            .map(|points_to_ty| (points_to_ty, reference))
                    })
                    .map(|(ref_points_to_ty, reference)| {
                        crate::stage::ast::TypedExprNode::Deref(ref_points_to_ty, Box::new(reference))
                    })
                    .ok_or_else(|| format!("invalid type for identifier({}) in scale operation", &identifier))
            }
        }
    }

    fn analyze_binary_expr(
        &self,
        lhs: crate::parser::ast::ExprNode,
        rhs: crate::parser::ast::ExprNode,
    ) -> Option<(crate::stage::ast::Type, crate::stage::ast::TypedExprNode, crate::stage::ast::TypedExprNode)> {
        let lhs = self.analyze_expression(lhs).unwrap();
        let rhs = self.analyze_expression(rhs).unwrap();

        match SmallestEncompassing.type_compatible(&lhs.r#type(), &rhs.r#type()) {
            CompatibilityResult::Equivalent => Some((lhs.r#type(), lhs, rhs)),
            CompatibilityResult::WidenTo(ty) => Some((ty, lhs, rhs)),
            CompatibilityResult::Incompatible => None,
            CompatibilityResult::Scale(ty) => Some((
                ty.pointer_to(),
                lhs,
                crate::stage::ast::TypedExprNode::ScaleBy(ty, Box::new(rhs)),
            )),
        }
    }

    fn analyze_inc_dec_expr(
        &self,
        variant: IncDecExpr,
        expr: crate::parser::ast::ExprNode,
    ) -> Result<crate::stage::ast::TypedExprNode, String> {
        use crate::stage::ast::TypedExprNode;
        self.analyze_expression(expr)
            .and_then(|ty_expr| match ty_expr {
                lvalue_expr @ TypedExprNode::Primary(_, crate::stage::ast::Primary::Identifier(_, _)) => {
                    Ok(lvalue_expr)
                }

                lvalue_expr @ TypedExprNode::Deref(_, _) => Ok(lvalue_expr),
                TypedExprNode::Grouping(ty, inner_expr) => {
                    let expr = *inner_expr;
                    if let TypedExprNode::Deref(ty, expr) = expr {
                        Ok(TypedExprNode::Deref(ty, expr))
                    } else {
                        Err(format!(
                            "type {:?} is not an lvalue",
                            TypedExprNode::Grouping(ty, Box::new(expr))
                        ))
                    }
                }

                // r-value expressions are not valid for ++/-- operators
                rvalue_expr => Err(format!("type {:?} is not an lvalue", rvalue_expr)),
            })
            .map(|expr| match variant {
                IncDecExpr::PreIncrement => {
                    TypedExprNode::PreIncrement(expr.r#type(), Box::new(expr))
                }
                IncDecExpr::PreDecrement => {
                    TypedExprNode::PreDecrement(expr.r#type(), Box::new(expr))
                }
                IncDecExpr::PostIncrement => {
                    TypedExprNode::PostIncrement(expr.r#type(), Box::new(expr))
                }
                IncDecExpr::PostDecrement => {
                    TypedExprNode::PostDecrement(expr.r#type(), Box::new(expr))
                }
            })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IncDecExpr {
    PreIncrement,
    PreDecrement,
    PostIncrement,
    PostDecrement,
}

#[cfg(test)]
mod tests {
    use crate::parser::ast;
    use crate::stage::{
        self,
       ast::{IdentifierLocality, IntegerWidth, Signed, Type, TypedExprNode},
    };

    macro_rules! pad_to_le_64bit_array {
        ($val:literal) => {
            $crate::util::pad_to_64bit_array($val.to_le_bytes())
        };
    }

    #[test]
    fn test_grouping_assigns_correct_type() {
        let analyzer = super::TypeAnalysis::default();
        let pre_typed_ast =
            ast::ExprNode::Grouping(Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::Eight,
                value: pad_to_le_64bit_array!(1u8),
            })));

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::Grouping(
            Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
            Box::new(TypedExprNode::Primary(
                Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                stage::ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
        );

        assert_eq!(Ok(expected), typed_ast);

        // Preserves complex order

        let pre_typed_ast = ast::ExprNode::Grouping(Box::new(ast::ExprNode::Multiplication(
            Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::Eight,
                value: pad_to_le_64bit_array!(2u8),
            })),
            Box::new(ast::ExprNode::Addition(
                Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(3u8),
                })),
                Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(4u8),
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
                        value: pad_to_le_64bit_array!(2u8),
                    },
                )),
                Box::new(TypedExprNode::Addition(
                    Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                    Box::new(TypedExprNode::Primary(
                        Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                        stage::ast::Primary::Integer {
                            sign: Signed::Unsigned,
                            width: IntegerWidth::Eight,
                            value: pad_to_le_64bit_array!(3u8),
                        },
                    )),
                    Box::new(TypedExprNode::Primary(
                        Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                        stage::ast::Primary::Integer {
                            sign: Signed::Unsigned,
                            width: IntegerWidth::Eight,
                            value: pad_to_le_64bit_array!(4u8),
                        },
                    )),
                )),
            )),
        );

        assert_eq!(Ok(expected), typed_ast);
    }

    #[test]
    fn test_string_assignment_correctly_assigns_pointer_ref() {
        use crate::stage::type_check::scopes;
        let mut analyzer = super::TypeAnalysis::default();
        let pre_typed_ast = assignment_expr!(
            ast::ExprNode::Primary(ast::Primary::Identifier("x".to_string())),
            '=',
            primary_expr!(str "hello")
        );

        // allocate x with predefined type prior to analysis
        analyzer.scopes.push_new_scope_mut();
        analyzer.scopes.define_local_mut(
            "x",
            generate_type_specifier!(char).pointer_to(),
            scopes::Kind::Basic,
        );

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::IdentifierAssignment(
            generate_type_specifier!(i8).pointer_to(),
            IdentifierLocality::Local(-8),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(i8).pointer_to(),
                stage::ast::Primary::Str("hello".chars().map(|c| c as u8).collect()),
            )),
        );

        assert_eq!(Ok(expected), typed_ast);
    }

    #[test]
    fn should_assign_nearest_ranked_size() {
        let analyzer = super::TypeAnalysis::default();

        // promotion of integer size

        let pre_typed_ast = ast::ExprNode::Addition(
            Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::Eight,
                value: pad_to_le_64bit_array!(1u8),
            })),
            Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                sign: Signed::Signed,
                width: IntegerWidth::Eight,
                value: pad_to_le_64bit_array!(1u8),
            })),
        );

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::Addition(
            generate_type_specifier!(i16),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u8),
                stage::ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(i8),
                stage::ast::Primary::Integer {
                    sign: Signed::Signed,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
        );

        assert_eq!(Ok(expected), typed_ast);

        // equivalent size

        let pre_typed_ast = ast::ExprNode::Addition(
            Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::Eight,
                value: pad_to_le_64bit_array!(1u8),
            })),
            Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::Eight,
                value: pad_to_le_64bit_array!(1u8),
            })),
        );

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::Addition(
            generate_type_specifier!(u8),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u8),
                stage::ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u8),
                stage::ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
        );

        assert_eq!(Ok(expected), typed_ast);
    }

    #[test]
    fn should_promote_a_larger_unsigned_int_to_signed_if_one_is_signed() {
        let analyzer = super::TypeAnalysis::default();

        let pre_typed_ast = ast::ExprNode::Addition(
            Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::ThirtyTwo,
                value: pad_to_le_64bit_array!(1u32),
            })),
            Box::new(ast::ExprNode::Primary(ast::Primary::Integer {
                sign: Signed::Signed,
                width: IntegerWidth::Eight,
                value: pad_to_le_64bit_array!(1u8),
            })),
        );

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::Addition(
            generate_type_specifier!(i64),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u32),
                stage::ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::ThirtyTwo,
                    value: pad_to_le_64bit_array!(1u32),
                },
            )),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(i8),
                stage::ast::Primary::Integer {
                    sign: Signed::Signed,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
        );

        assert_eq!(Ok(expected), typed_ast);
    }
}
