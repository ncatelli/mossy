//! The Type Pass module handles walking the raw parser ADT, performing
//! additional type checking and enrichment.

use mossy_parser::parser;

use crate::stage::type_check::ast::DefinitionState;

use super::CompilationStage;

#[macro_use]
pub mod ast;
use ast::{FunctionSignature, Type, Typed};

mod scopes;
use scopes::ScopeStack;

#[derive(Clone, Copy, PartialEq, Eq)]
struct Integer {
    signed: ast::Signed,
    width: ast::IntegerWidth,
}

impl Integer {
    fn new(signed: ast::Signed, width: ast::IntegerWidth) -> Self {
        Self { signed, width }
    }
}

impl std::convert::TryFrom<usize> for Integer {
    type Error = String;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        use ast::{IntegerWidth, Signed};
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

impl Ranking for ast::Signed {
    type Output = usize;

    fn rank(&self) -> Self::Output {
        match self {
            ast::Signed::Signed => 0,
            ast::Signed::Unsigned => 1,
        }
    }
}

impl Ranking for ast::IntegerWidth {
    type Output = usize;

    fn rank(&self) -> Self::Output {
        match self {
            ast::IntegerWidth::One => 0,
            ast::IntegerWidth::Eight => 2,
            ast::IntegerWidth::Sixteen => 4,
            ast::IntegerWidth::ThirtyTwo => 6,
            ast::IntegerWidth::SixtyFour => 8,
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
    WidenTo(ast::Type),
    Scale(ast::Type),
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
    type Lhs = Type;
    type Rhs = Type;

    fn type_compatible(&self, lhs: &Self::Lhs, rhs: &Self::Rhs) -> Self::Output {
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
    type Lhs = Type;
    type Rhs = Type;

    fn type_compatible(&self, lhs: &Self::Lhs, rhs: &Self::Rhs) -> Self::Output {
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
    in_func: Option<(String, ast::FunctionSignature)>,
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

impl CompilationStage<parser::ast::CompilationUnit, ast::TypedProgram, String>
    for TypeAnalysis
{
    fn apply(
        &mut self,
        input: parser::ast::CompilationUnit,
    ) -> Result<ast::TypedProgram, String> {
        input
            .defs
            .into_iter()
            .map(|ast_node| self.apply(ast_node))
            .collect::<Result<Vec<ast::TypedGlobalDecls>, String>>()
            .map(ast::TypedProgram::new)
    }
}

impl CompilationStage<parser::ast::GlobalDecls, ast::TypedGlobalDecls, String>
    for TypeAnalysis
{
    fn apply(
        &mut self,
        input: parser::ast::GlobalDecls,
    ) -> Result<ast::TypedGlobalDecls, String> {
        use scopes::DeclarationMetadata;

        match input {
            parser::ast::GlobalDecls::FuncDefinition(fd) => {
                let (id, return_ty, block) = (fd.proto.id, fd.proto.return_type, fd.block);
                let params = fd.proto.params.into_iter().map(Into::into).collect();
                let new_sig = FunctionSignature::new(Box::new(return_ty.into()), params);

                match self.scopes.lookup(&id) {
                    // clobbers non-existent function.
                    Some(DeclarationMetadata { ty, .. })
                        if !matches!(ty.clone(), Type::Func(_)) =>
                    {
                        Err(format!(
                            "function {} redefines conflicting type: {:?}",
                            &id, ty
                        ))
                    }
                    // clobbers already defined function.
                    Some(DeclarationMetadata {
                        definition_state: DefinitionState::Defined,
                        ty,
                        ..
                    }) if matches!(ty.clone(), Type::Func(_)) => {
                        Err(format!("function {} defined multiple times", &id))
                    }
                    Some(DeclarationMetadata {
                        definition_state: DefinitionState::Declared,
                        ty: Type::Func(previous_sig),
                        ..
                    }) if previous_sig != new_sig => Err(format!(
                        "function {} conflicts with previous declaration: {:?}",
                        &id, &previous_sig
                    )),
                    // declared previously and matching the signature
                    Some(DeclarationMetadata {
                        definition_state: DefinitionState::Declared,
                        ty: Type::Func(previous_sig),
                        ..
                    }) if previous_sig == new_sig => {
                        let type_proto = ast::Type::Func(new_sig.clone());
                        self.scopes
                            .define_global_mut(&id, type_proto, scopes::Kind::Basic);

                        self.analyze_function_body(id.clone(), new_sig, block)
                            .map(ast::TypedGlobalDecls::Func)
                    }
                    // undeclared/undefined safe to redefine.
                    None => {
                        let type_proto = ast::Type::Func(new_sig.clone());
                        self.scopes
                            .define_global_mut(&id, type_proto, scopes::Kind::Basic);

                        self.analyze_function_body(id.clone(), new_sig, block)
                            .map(ast::TypedGlobalDecls::Func)
                    }
                    // all posible cases otherwise should be covered
                    _ => unreachable!(),
                }
            }
            parser::ast::GlobalDecls::Var(parser::ast::Declaration::Scalar(ty, ids)) => {
                let ty = ast::Type::from(ty);

                for id in ids.iter() {
                    self.scopes
                        .declare_global_mut(id, ty.clone(), scopes::Kind::Basic);
                }

                Ok(ast::TypedGlobalDecls::Var(ast::Declaration::Scalar(
                    ty, ids,
                )))
            }
            parser::ast::GlobalDecls::Var(parser::ast::Declaration::Array { ty, id, size }) => {
                let ty = ast::Type::from(ty);

                self.scopes
                    .declare_global_mut(&id,ty.pointer_to(), scopes::Kind::Array(size));

                Ok(ast::TypedGlobalDecls::Var(ast::Declaration::Array {
                    ty,
                    id,
                    size,
                }))
            }
            parser::ast::GlobalDecls::FuncProto(proto) => {
                let (id, return_ty) = (proto.id, proto.return_type.into());
                let params = proto
                    .params
                    .into_iter()
                    .map(ast::Parameter::from)
                    .collect();

                let new_sig = FunctionSignature::new(Box::new(return_ty), params);

                match self.scopes.lookup(&id) {
                    // clobbers non-existent function.
                    Some(DeclarationMetadata { ty, .. })
                        if !(matches!(ty.clone(), Type::Func(_))) =>
                    {
                        Err(format!(
                            "function {} redefines conflicting type: {:?}",
                            &id, ty
                        ))
                    }
                    // clobbers already defined function.
                    Some(DeclarationMetadata { definition_state:ast::DefinitionState::Defined ,ty, .. })
                        if matches!(ty.clone(), Type::Func( _)) =>
                    {
                        Err(format!("function {} already defined", &id))
                    }
                    Some(DeclarationMetadata {
                        definition_state:ast::DefinitionState::Declared, 
                        ty: Type::Func( previous_sig),
                        ..
                    }) if previous_sig != new_sig => {
                        Err(format!("declaration of function signature {:?} conflicts with previous declaration: {:?}", &new_sig, &previous_sig))
                    }
                    // if already declared, do nothing.
                    Some(DeclarationMetadata {
                        definition_state: ast::DefinitionState::Declared,
                        ty: Type::Func( previous_sig),
                        ..
                    }) if previous_sig == new_sig => Ok(ast::TypedGlobalDecls::FuncProto),
                    // if undeclared/undefined, declare the function.
                    None => {
                        let type_proto = ast::Type::Func(new_sig);
                        self.scopes
                            .declare_global_mut(&id, type_proto, scopes::Kind::Basic);

                        Ok(ast::TypedGlobalDecls::FuncProto)
                    }
                    // all posible cases otherwise should be covered
                    _ => unreachable!(),
                }
            }
        }
    }
}

impl TypeAnalysis {
    fn analyze_function_body(
        &mut self,
        id: String,
        func_proto: FunctionSignature,
        block: parser::ast::CompoundStmts,
    ) -> Result<ast::TypedFunctionDeclaration, String> {
        let old_body = self.in_func.replace((id.clone(), func_proto.clone()));
        self.scopes.push_new_scope_mut();
        let stmts = Vec::from(block);
        let mut typed_stmts = vec![];

        // Declare global parameters prior to statement analysis
        for param in func_proto.parameters.iter() {
            self.scopes
                .declare_parameter_mut(&param.id, param.ty.clone(), scopes::Kind::Basic);
        }

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

        let params = self
            .scopes
            .local_scope()
            .map(|s| s.ordered_parameter_declarations())
            // safe to unwrap due to guarantee of local scope
            .unwrap();

        let local_vars = self
            .scopes
            .local_scope()
            .map(|s| s.ordered_local_declarations())
            // safe to unwrap due to guarantee of local scope
            .unwrap();

        // reset scope
        self.scopes.pop_scope_mut();
        self.in_func = old_body;

        let block = ast::TypedCompoundStmts::new(typed_stmts);

        Ok(ast::TypedFunctionDeclaration::new(
            id, block, params, local_vars,
        ))
    }

    fn analyze_block(
        &mut self,
        block: parser::ast::CompoundStmts,
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
        input: parser::ast::StmtNode,
    ) -> Result<ast::TypedStmtNode, String> {
        match input {
            parser::ast::StmtNode::Expression(expr) => self
                .analyze_expression(expr)
                .map(ast::TypedStmtNode::Expression),
            parser::ast::StmtNode::Declaration(parser::ast::Declaration::Scalar(ty, ids)) => {
                let slot_ids = ids
                    .iter()
                    .map(|id| {
                        self.scopes
                            .declare_local_mut(id, ty.clone().into(), scopes::Kind::Basic)
                    })
                    .collect();

                Ok(ast::TypedStmtNode::LocalDeclaration(
                    ast::Declaration::Scalar(ty.into(), ids),
                    slot_ids,
                ))
            }
            parser::ast::StmtNode::Declaration(parser::ast::Declaration::Array {
                ty,
                id,
                size,
            }) => {
let ty = ast::Type::from(ty);

                let slot_ids = self.scopes.declare_local_mut(
                    &id,
                    ty.pointer_to(),
                    scopes::Kind::Array(size),
                );

                Ok(ast::TypedStmtNode::LocalDeclaration(
                    ast::Declaration::Array {
                        ty,
                        id,
                        size,
                    },
                    vec![slot_ids],
                ))
            }
            parser::ast::StmtNode::Return(Some(rt_expr)) => {
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

                    Ok(ast::TypedStmtNode::Return(
                        rt_type,
                        id.to_owned(),
                        Some(typed_expr),
                    ))
                } else {
                    Err("invalid use of return: not in function".to_string())
                }
            }
            parser::ast::StmtNode::Return(None) => {
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

            parser::ast::StmtNode::If(cond, t_case, f_case) => {
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
            parser::ast::StmtNode::While(cond, block) => {
                let typed_cond = self.analyze_expression(cond)?;
                let typed_block = self.analyze_block(block)?;

                Ok(ast::TypedStmtNode::While(typed_cond, typed_block))
            }
            parser::ast::StmtNode::For(preop, cond, postop, block) => {
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
        expr: parser::ast::ExprNode,
    ) -> Result<ast::TypedExprNode, String> {
        use parser::ast::ExprNode;
        use parser::ast::Primary;

        match expr {
            ExprNode::Primary(Primary::Integer { sign, width, value }) => {
                let (sign, width) = (sign.into(), width.into());
                Ok(ast::TypedExprNode::Primary(
                    ast::Type::Integer(sign, width),
                    ast::Primary::Integer {
                        sign: sign.into(),
                        width: width.into(),
                        value,
                    },
                ))
            }
            ExprNode::Primary(Primary::Identifier(identifier)) => self
                .scopes
                .lookup(&identifier)
                .ok_or_else(|| format!("identifier ({}) undefined", &identifier))
                .map(|dm| match (dm.is_array(), dm.locality) {
                    (true, scopes::Locality::Global) => {
                        ast::TypedExprNode::Ref(dm.ty, ast::IdentifierLocality::Global(identifier))
                    }
                    (false, scopes::Locality::Global) => ast::TypedExprNode::Primary(
                        dm.ty.clone(),
                        ast::Primary::Identifier(
                            dm.ty,
                            ast::IdentifierLocality::Global(identifier),
                        ),
                    ),
                    (true, scopes::Locality::Local(slot)) => {
                        ast::TypedExprNode::Ref(dm.ty, ast::IdentifierLocality::Local(slot))
                    }
                    (false, scopes::Locality::Local(slot)) => ast::TypedExprNode::Primary(
                        dm.ty.clone(),
                        ast::Primary::Identifier(dm.ty, ast::IdentifierLocality::Local(slot)),
                    ),
                    (true, scopes::Locality::Parameter(slot)) => {
                        ast::TypedExprNode::Ref(dm.ty, ast::IdentifierLocality::Parameter(slot))
                    }
                    (false, scopes::Locality::Parameter(slot)) => ast::TypedExprNode::Primary(
                        dm.ty.clone(),
                        ast::Primary::Identifier(dm.ty, ast::IdentifierLocality::Parameter(slot)),
                    ),
                }),
            ExprNode::Primary(Primary::Str(elems)) => Ok(ast::TypedExprNode::Primary(
                generate_type_specifier!(ptr => generate_type_specifier!(char)),
                ast::Primary::Str(elems),
            )),

            ExprNode::Grouping(expr) => self
                .analyze_expression(*expr)
                .map(|ty_expr| (ty_expr.r#type(), ty_expr))
                .map(|(ty, expr)| ast::TypedExprNode::Grouping(ty, Box::new(expr))),

            ExprNode::FunctionCall(identifier, args) => {
                let args = args
                    .into_iter()
                    .map(|arg| self.analyze_expression(arg))
                    .collect::<Result<Vec<_>, _>>()?;

                let args_type_sig: Vec<ast::Type> = args.iter().map(|arg| arg.r#type()).collect();

                self.scopes
                    .lookup(&identifier)
                    .ok_or_else(|| format!("undefined_function: {}", &identifier))
                    .and_then(|dm| match dm.ty.clone() {
                        ast::Type::Func(FunctionSignature {
                            return_type,
                            parameters: params,
                        }) => {
                            let params_type_sig = params.iter().map(|arg| arg.ty.clone());

                            if params_type_sig.len() == args_type_sig.len() {
                                let adjusted_arg_types = params_type_sig
                                    .zip(args_type_sig.iter())
                                    .map(|(param_ty, arg_ty)| {
                                        match LeftFlowing.type_compatible(&param_ty, arg_ty) {
                                            CompatibilityResult::Equivalent => Ok(param_ty.clone()),
                                            CompatibilityResult::WidenTo(ty) => Ok(ty),
                                            CompatibilityResult::Scale(_)
                                            | CompatibilityResult::Incompatible => Err(format!(
                                                "incompatible parameter type for {} function call {:?} <- {:?}",
                                                &identifier, &param_ty, &arg_ty
                                            )),
                                        }
                                    })
                                    .collect::<Result<Vec<_>, _>>()
                                    .map_err(|e| e)?;

                                let adjusted_args = adjusted_arg_types.into_iter().zip(args.into_iter()).map(|(expr_ty, expr)| {
                                    ast::TypedExprNode::Grouping(expr_ty, Box::new(expr))
                                }).collect();

                                Ok(ast::TypedExprNode::FunctionCall(
                                    *return_type,
                                    identifier,
                                    adjusted_args,
                                ))
                            } else {
                                Err(format!(
                                    "type mismatch, cannot call non-function type: {:?} with: {:?}",
                                    &dm.ty, args_type_sig
                                ))
                            }
                        }
                        _ => Err(format!(
                            "type mismatch, cannot call non-function type: {:?}",
                            &dm.ty
                        )),
                    })
            }

            ExprNode::Assignment(lhs, rhs) => {
                use ast::{Primary, TypedExprNode};

                let rhs = self.analyze_expression(*rhs)?;
                let lhs = self.analyze_expression(*lhs)?;

                match lhs {
                    TypedExprNode::Primary(lhs_ty, Primary::Identifier(_, ast::IdentifierLocality::Global(id))) => self
                        .scopes
                        .lookup(&id)
                        .map(|dm| LeftFlowing.type_compatible(&dm.ty, &rhs.r#type()))
                        .ok_or(format!("symbol {} undefined", &id))
                        .and_then(|type_compat| match type_compat {
                            CompatibilityResult::Equivalent => Ok(lhs_ty),
                            CompatibilityResult::WidenTo(ty) => Ok(ty),
                            CompatibilityResult::Incompatible => {
                                Err(format!("invalid type in identifier lookup for ({}):\n\texpected: lhs({:?})\n\tgot: rhs({:?})", &id, lhs_ty, &rhs.r#type()))
                            }
                            CompatibilityResult::Scale(t) => Ok(t),
                        })
                        .map(|ty| ast::TypedExprNode::IdentifierAssignment(ty, ast::IdentifierLocality::Global(id), Box::new(rhs))),
                    TypedExprNode::Primary(lhs_ty, Primary::Identifier(ty, ast::IdentifierLocality::Local(offset))) => {
                        let type_compat = LeftFlowing.type_compatible(&ty, &rhs.r#type());
                         match type_compat {
                            CompatibilityResult::Equivalent => Ok(lhs_ty),
                            CompatibilityResult::WidenTo(ty) => Ok(ty),
                            CompatibilityResult::Incompatible => {
                                Err(format!("invalid type in identifier:\n\texpected: lhs({:?})\n\tgot: rhs({:?})", lhs_ty, &rhs.r#type()))
                            }
                            CompatibilityResult::Scale(t) => Ok(t),
                        }
                        .map(|ty| ast::TypedExprNode::IdentifierAssignment(ty, ast::IdentifierLocality::Local(offset), Box::new(rhs)))
                    }
                    TypedExprNode::Primary(lhs_ty, Primary::Identifier(ty, ast::IdentifierLocality::Parameter(offset))) => {
                        let type_compat = LeftFlowing.type_compatible(&ty, &rhs.r#type());
                         match type_compat {
                            CompatibilityResult::Equivalent => Ok(lhs_ty),
                            CompatibilityResult::WidenTo(ty) => Ok(ty),
                            CompatibilityResult::Incompatible => {
                                Err(format!("invalid type in identifier:\n\texpected: lhs({:?})\n\tgot: rhs({:?})", lhs_ty, &rhs.r#type()))
                            }
                            CompatibilityResult::Scale(t) => Ok(t),
                        }
                        .map(|ty| ast::TypedExprNode::IdentifierAssignment(ty, ast::IdentifierLocality::Parameter(offset), Box::new(rhs)))
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
                    .map(|ty| ast::TypedExprNode::DerefAssignment(ty, expr, Box::new(rhs))),
                    // Fail on any other type
                    _ => Err(format!("invalid assignment type: ({:?})", lhs.r#type())),
                }
            }

            ExprNode::LogOr(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(_, lhs, rhs)| {
                    let ty = ast::Type::Integer(ast::Signed::Unsigned, ast::IntegerWidth::One);
                    ast::TypedExprNode::LogOr(ty, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "incompatible types for logical or comparison".to_string()),
            ExprNode::LogAnd(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(_, lhs, rhs)| {
                    let ty = ast::Type::Integer(ast::Signed::Unsigned, ast::IntegerWidth::One);
                    ast::TypedExprNode::LogAnd(ty, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "incompatible types for logical and comparison".to_string()),

            ExprNode::BitOr(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(ty, lhs, rhs)| ast::TypedExprNode::BitOr(ty, Box::new(lhs), Box::new(rhs)))
                .ok_or_else(|| "incompatible types for bitwise or operation".to_string()),
            ExprNode::BitXor(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(ty, lhs, rhs)| ast::TypedExprNode::BitXor(ty, Box::new(lhs), Box::new(rhs)))
                .ok_or_else(|| "incompatible types for bitwise xor operation".to_string()),
            ExprNode::BitAnd(lhs, rhs) => self
                .analyze_binary_expr(*lhs, *rhs)
                .map(|(ty, lhs, rhs)| ast::TypedExprNode::BitAnd(ty, Box::new(lhs), Box::new(rhs)))
                .ok_or_else(|| "incompatible types for bitwise and operation".to_string()),

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
                    ast::TypedExprNode::BitShiftLeft(expr_type, Box::new(lhs), Box::new(rhs))
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
                    ast::TypedExprNode::BitShiftRight(expr_type, Box::new(lhs), Box::new(rhs))
                })
                .ok_or_else(|| "incompatible operands to right shift operation".to_string()),

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

            ExprNode::LogicalNot(expr) => self
                .analyze_expression(*expr)
                .map(|expr| (expr.r#type(), expr))
                .map(|(expr_type, expr)| ast::TypedExprNode::LogicalNot(expr_type, Box::new(expr))),
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
                .map(|(expr_type, expr)| ast::TypedExprNode::Negate(expr_type, Box::new(expr))),
            ExprNode::Invert(expr) => self
                .analyze_expression(*expr)
                .map(|expr| (expr.r#type(), expr))
                .map(|(expr_type, expr)| ast::TypedExprNode::Invert(expr_type, Box::new(expr))),

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
                .map(|dm| match dm.locality {
                    scopes::Locality::Global => ast::TypedExprNode::Ref(
                        dm.ty.pointer_to(),
                        ast::IdentifierLocality::Global(identifier),
                    ),
                    scopes::Locality::Local(slot) => ast::TypedExprNode::Ref(
                        dm.ty.pointer_to(),
                        ast::IdentifierLocality::Local(slot),
                    ),
                    scopes::Locality::Parameter(slot) => ast::TypedExprNode::Ref(
                        dm.ty.pointer_to(),
                        ast::IdentifierLocality::Parameter(slot),
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
                .map(|(ty, expr)| ast::TypedExprNode::Deref(ty, Box::new(expr))),
            ExprNode::Index(identifier, index) => {
                let ptr_width =
                    ast::Type::Integer(ast::Signed::Signed, ast::IntegerWidth::SixtyFour);

                let index_expr = self.analyze_expression(*index)?;
                let index_expr_ty = &index_expr.r#type();

                let index_expr =
                    match LeftFlowing.type_compatible(&ptr_width, &index_expr.r#type()) {
                        CompatibilityResult::Equivalent => Some(index_expr),
                        CompatibilityResult::WidenTo(ty) => {
                            Some(ast::TypedExprNode::Grouping(ty, Box::new(index_expr)))
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
                        reference.ty.value_at().map(|value_of_ref| {
                            (
                                reference,
                                ast::TypedExprNode::ScaleBy(value_of_ref, Box::new(index_expr)),
                            )
                        })
                    })
                    .map(|(dm, scale)| {
                        let ref_ty = dm.ty.clone();

                        let l_value_access = match (dm.is_array(), dm.locality) {
                            (true, scopes::Locality::Global) => Box::new(ast::TypedExprNode::Ref(
                                ref_ty.clone(),
                                ast::IdentifierLocality::Global(identifier.clone()),
                            )),
                            (false, scopes::Locality::Global) => {
                                Box::new(ast::TypedExprNode::Primary(
                                    ref_ty.clone(),
                                    ast::Primary::Identifier(
                                        ref_ty.clone(),
                                        ast::IdentifierLocality::Global(identifier.clone()),
                                    ),
                                ))
                            }
                            (true, scopes::Locality::Local(offset)) => {
                                Box::new(ast::TypedExprNode::Ref(
                                    ref_ty.clone(),
                                    ast::IdentifierLocality::Local(offset),
                                ))
                            }
                            (false, scopes::Locality::Local(offset)) => {
                                Box::new(ast::TypedExprNode::Primary(
                                    ref_ty.clone(),
                                    ast::Primary::Identifier(
                                        ref_ty.clone(),
                                        ast::IdentifierLocality::Local(offset),
                                    ),
                                ))
                            }
                            (true, scopes::Locality::Parameter(_)) => todo!(),
                            (false, scopes::Locality::Parameter(_)) => todo!(),
                        };

                        ast::TypedExprNode::Addition(ref_ty, l_value_access, Box::new(scale))
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
                    .ok_or_else(|| {
                        format!(
                            "invalid type for identifier({}) in scale operation",
                            &identifier
                        )
                    })
            }
        }
    }

    fn analyze_binary_expr(
        &self,
        lhs: parser::ast::ExprNode,
        rhs: parser::ast::ExprNode,
    ) -> Option<(ast::Type, ast::TypedExprNode, ast::TypedExprNode)> {
        let lhs = self.analyze_expression(lhs).unwrap();
        let rhs = self.analyze_expression(rhs).unwrap();

        match SmallestEncompassing.type_compatible(&lhs.r#type(), &rhs.r#type()) {
            CompatibilityResult::Equivalent => Some((lhs.r#type(), lhs, rhs)),
            CompatibilityResult::WidenTo(ty) => Some((ty, lhs, rhs)),
            CompatibilityResult::Incompatible => None,
            CompatibilityResult::Scale(ty) => Some((
                ty.pointer_to(),
                lhs,
                ast::TypedExprNode::ScaleBy(ty, Box::new(rhs)),
            )),
        }
    }

    fn analyze_inc_dec_expr(
        &self,
        variant: IncDecExpr,
        expr: parser::ast::ExprNode,
    ) -> Result<ast::TypedExprNode, String> {
        use ast::TypedExprNode;
        self.analyze_expression(expr)
            .and_then(|ty_expr| match ty_expr {
                lvalue_expr @ TypedExprNode::Primary(_, ast::Primary::Identifier(_, _)) => {
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
    use super::ast::{IdentifierLocality, IntegerWidth, Signed, Type, TypedExprNode};
    use mossy_parser::parser;

    use mossy_parser::{assignment_expr, primary_expr};

    macro_rules! pad_to_le_64bit_array {
        ($val:literal) => {
            $crate::util::pad_to_64bit_array($val.to_le_bytes())
        };
    }

    #[test]
    fn test_grouping_assigns_correct_type() {
        let analyzer = super::TypeAnalysis::default();
        let pre_typed_ast = parser::ast::ExprNode::Grouping(Box::new(
            parser::ast::ExprNode::Primary(parser::ast::Primary::Integer {
                sign: parser::ast::Signed::Unsigned,
                width: parser::ast::IntegerWidth::Eight,
                value: pad_to_le_64bit_array!(1u8),
            }),
        ));

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::Grouping(
            Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
            Box::new(TypedExprNode::Primary(
                Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                super::ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
        );

        assert_eq!(Ok(expected), typed_ast);

        // Preserves complex order

        let pre_typed_ast =
            parser::ast::ExprNode::Grouping(Box::new(parser::ast::ExprNode::Multiplication(
                Box::new(parser::ast::ExprNode::Primary(
                    parser::ast::Primary::Integer {
                        sign: parser::ast::Signed::Unsigned,
                        width: parser::ast::IntegerWidth::Eight,
                        value: pad_to_le_64bit_array!(2u8),
                    },
                )),
                Box::new(parser::ast::ExprNode::Addition(
                    Box::new(parser::ast::ExprNode::Primary(
                        parser::ast::Primary::Integer {
                            sign: parser::ast::Signed::Unsigned,
                            width: parser::ast::IntegerWidth::Eight,
                            value: pad_to_le_64bit_array!(3u8),
                        },
                    )),
                    Box::new(parser::ast::ExprNode::Primary(
                        parser::ast::Primary::Integer {
                            sign: parser::ast::Signed::Unsigned,
                            width: parser::ast::IntegerWidth::Eight,
                            value: pad_to_le_64bit_array!(4u8),
                        },
                    )),
                )),
            )));

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::Grouping(
            Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
            Box::new(TypedExprNode::Multiplication(
                Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                Box::new(TypedExprNode::Primary(
                    Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                    super::ast::Primary::Integer {
                        sign: Signed::Unsigned,
                        width: IntegerWidth::Eight,
                        value: pad_to_le_64bit_array!(2u8),
                    },
                )),
                Box::new(TypedExprNode::Addition(
                    Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                    Box::new(TypedExprNode::Primary(
                        Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                        super::ast::Primary::Integer {
                            sign: Signed::Unsigned,
                            width: IntegerWidth::Eight,
                            value: pad_to_le_64bit_array!(3u8),
                        },
                    )),
                    Box::new(TypedExprNode::Primary(
                        Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
                        super::ast::Primary::Integer {
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
            parser::ast::ExprNode::Primary(parser::ast::Primary::Identifier("x".to_string())),
            '=',
            primary_expr!(str "hello")
        );

        // allocate x with predefined type prior to analysis
        analyzer.scopes.push_new_scope_mut();
        analyzer.scopes.declare_local_mut(
            "x",
            generate_type_specifier!(char).pointer_to(),
            scopes::Kind::Basic,
        );

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::IdentifierAssignment(
            generate_type_specifier!(i8).pointer_to(),
            IdentifierLocality::Local(0),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(i8).pointer_to(),
                super::ast::Primary::Str("hello".chars().map(|c| c as u8).collect()),
            )),
        );

        assert_eq!(Ok(expected), typed_ast);
    }

    #[test]
    fn should_assign_nearest_ranked_size() {
        let analyzer = super::TypeAnalysis::default();

        // promotion of integer size

        let pre_typed_ast = parser::ast::ExprNode::Addition(
            Box::new(parser::ast::ExprNode::Primary(
                parser::ast::Primary::Integer {
                    sign: parser::ast::Signed::Unsigned,
                    width: parser::ast::IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
            Box::new(parser::ast::ExprNode::Primary(
                parser::ast::Primary::Integer {
                    sign: parser::ast::Signed::Signed,
                    width: parser::ast::IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
        );

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::Addition(
            generate_type_specifier!(i16),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u8),
                super::ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(i8),
                super::ast::Primary::Integer {
                    sign: Signed::Signed,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
        );

        assert_eq!(Ok(expected), typed_ast);

        // equivalent size

        let pre_typed_ast = parser::ast::ExprNode::Addition(
            Box::new(parser::ast::ExprNode::Primary(
                parser::ast::Primary::Integer {
                    sign: parser::ast::Signed::Unsigned,
                    width: parser::ast::IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
            Box::new(parser::ast::ExprNode::Primary(
                parser::ast::Primary::Integer {
                    sign: parser::ast::Signed::Unsigned,
                    width: parser::ast::IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
        );

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::Addition(
            generate_type_specifier!(u8),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u8),
                super::ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u8),
                super::ast::Primary::Integer {
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

        let pre_typed_ast = parser::ast::ExprNode::Addition(
            Box::new(parser::ast::ExprNode::Primary(
                parser::ast::Primary::Integer {
                    sign: parser::ast::Signed::Unsigned,
                    width: parser::ast::IntegerWidth::ThirtyTwo,
                    value: pad_to_le_64bit_array!(1u32),
                },
            )),
            Box::new(parser::ast::ExprNode::Primary(
                parser::ast::Primary::Integer {
                    sign: parser::ast::Signed::Signed,
                    width: parser::ast::IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
        );

        let typed_ast = analyzer.analyze_expression(pre_typed_ast);
        let expected = TypedExprNode::Addition(
            generate_type_specifier!(i64),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(u32),
                super::ast::Primary::Integer {
                    sign: Signed::Unsigned,
                    width: IntegerWidth::ThirtyTwo,
                    value: pad_to_le_64bit_array!(1u32),
                },
            )),
            Box::new(TypedExprNode::Primary(
                generate_type_specifier!(i8),
                super::ast::Primary::Integer {
                    sign: Signed::Signed,
                    width: IntegerWidth::Eight,
                    value: pad_to_le_64bit_array!(1u8),
                },
            )),
        );

        assert_eq!(Ok(expected), typed_ast);
    }
}
