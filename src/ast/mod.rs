pub type Span = std::ops::Range<usize>;

#[derive(PartialEq, Debug, Clone)]
pub struct TypedFunctionDeclaration {
    pub id: String,
    pub block: TypedCompoundStmts,
}

impl TypedFunctionDeclaration {
    pub fn new(id: String, block: TypedCompoundStmts) -> Self {
        Self { id, block }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct TypedCompoundStmts {
    inner: Vec<TypedStmtNode>,
}

impl TypedCompoundStmts {
    pub fn new(inner: Vec<TypedStmtNode>) -> Self {
        Self { inner }
    }
}

impl From<TypedCompoundStmts> for Vec<TypedStmtNode> {
    fn from(src: TypedCompoundStmts) -> Self {
        src.inner
    }
}

/// AstNode representing any allowable statement in the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum TypedStmtNode {
    /// Declaration represents a global declaration statement with the
    /// enclosed string representing the Id of the variable.
    Declaration(Type, String),
    /// Assignment represents an assignment statement of an expressions value
    /// to a given pre-declared assignment.
    Assignment(String, TypedExprNode),
    /// Represents a statement containing only a single expression.
    Expression(TypedExprNode),
    /// Represents a conditional if statement with an optional else clause.
    If(
        TypedExprNode,
        TypedCompoundStmts,
        Option<TypedCompoundStmts>,
    ),
    /// Represents a while loop.
    While(TypedExprNode, TypedCompoundStmts),
    For(
        Box<TypedStmtNode>,
        TypedExprNode,
        Box<TypedStmtNode>,
        TypedCompoundStmts,
    ),
}

/// Represents a single expression in the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum TypedExprNode {
    Primary(Type, Primary),

    // Comparative
    Equal(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    NotEqual(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    LessThan(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    GreaterThan(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    LessEqual(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    GreaterEqual(Type, Box<TypedExprNode>, Box<TypedExprNode>),

    // Arithmetic
    Subtraction(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    Division(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    Addition(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    Multiplication(Type, Box<TypedExprNode>, Box<TypedExprNode>),
}

impl Typed for TypedExprNode {
    fn r#type(&self) -> Type {
        match self {
            TypedExprNode::Primary(t, _)
            | TypedExprNode::Equal(t, _, _)
            | TypedExprNode::NotEqual(t, _, _)
            | TypedExprNode::LessThan(t, _, _)
            | TypedExprNode::GreaterThan(t, _, _)
            | TypedExprNode::LessEqual(t, _, _)
            | TypedExprNode::GreaterEqual(t, _, _)
            | TypedExprNode::Subtraction(t, _, _)
            | TypedExprNode::Division(t, _, _)
            | TypedExprNode::Addition(t, _, _)
            | TypedExprNode::Multiplication(t, _, _) => t.clone(),
        }
    }
}

/// Primary represents a primitive type within the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum Primary {
    Integer {
        sign: Signed,
        width: IntegerWidth,
        value: u64,
    },
    Identifier(Type, String),
}

impl Typed for Primary {
    fn r#type(&self) -> Type {
        match self {
            Primary::Integer {
                sign: Signed::Unsigned,
                width: IntegerWidth::Eight,
                value: _,
            } => Type::Integer(Signed::Unsigned, IntegerWidth::Eight),
            Primary::Identifier(ty, _) => ty.clone(),
            _ => panic!("unknown type"),
        }
    }
}

/// Represents an object that contains a representable size in bytes.
pub trait ByteSized {
    fn size(&self) -> usize;
}

pub enum CompatibilityResult {
    Equivalent,
    WidenTo(Type),
    Incompatible,
}

/// Represents an object that contains a representable size in bytes.
pub trait Typed {
    fn r#type(&self) -> Type;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Signed {
    Signed,
    Unsigned,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntegerWidth {
    Eight,
}

impl ByteSized for IntegerWidth {
    fn size(&self) -> usize {
        match self {
            Self::Eight => 1,
        }
    }
}

/// Represents valid primitive types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Integer(Signed, IntegerWidth),
    Char,
    Void,
    Func { return_type: Box<Type> },
}

impl ByteSized for Type {
    fn size(&self) -> usize {
        match self {
            Type::Integer(_, iw) => iw.size(),
            Type::Char => 1,
            Type::Void => 0,
            &Type::Func { .. } => (usize::BITS / 8) as usize,
        }
    }
}

pub(crate) fn type_compatible(left: Type, right: Type, flow_left: bool) -> CompatibilityResult {
    match (left, right) {
        (lhs, rhs) if lhs == rhs => CompatibilityResult::Equivalent,
        (Type::Integer(sign, width), Type::Char) => {
            CompatibilityResult::WidenTo(Type::Integer(sign, width))
        }
        (Type::Char, Type::Integer(sign, width)) if !flow_left => {
            CompatibilityResult::WidenTo(Type::Integer(sign, width))
        }
        _ => CompatibilityResult::Incompatible,
    }
}
