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
            | TypedExprNode::Multiplication(t, _, _) => *t,
        }
    }
}

/// Primary represents a primitive type within the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum Primary {
    Uint8(Uint8),
    Identifier(Type, String),
}

impl Typed for Primary {
    fn r#type(&self) -> Type {
        match self {
            Primary::Uint8(_) => Type::Uint8,
            Primary::Identifier(kind, _) => *kind,
        }
    }
}

/// represents an 8-bit unsigned integer.
#[derive(PartialEq, Debug, Clone)]
pub struct Uint8(pub u8);

impl std::fmt::Display for Uint8 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Typed for Uint8 {
    fn r#type(&self) -> Type {
        Type::Uint8
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

/// Represents valid primitive types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Uint8,
    Char,
    Void,
}

impl ByteSized for Type {
    fn size(&self) -> usize {
        match self {
            Type::Uint8 | Type::Char => 1,
            Type::Void => 0,
        }
    }
}

pub(crate) fn type_compatible(left: Type, right: Type, flow_left: bool) -> CompatibilityResult {
    match (left, right) {
        _ if left == right => CompatibilityResult::Equivalent,
        (Type::Uint8, Type::Char) => CompatibilityResult::WidenTo(Type::Uint8),
        (Type::Char, Type::Uint8) if !flow_left => CompatibilityResult::WidenTo(Type::Uint8),
        _ => CompatibilityResult::Incompatible,
    }
}
