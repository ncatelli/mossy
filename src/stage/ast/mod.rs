#[derive(Debug)]
pub struct TypedProgram {
    pub defs: Vec<TypedGlobalDecls>,
}

impl TypedProgram {
    pub fn new(defs: Vec<TypedGlobalDecls>) -> Self {
        Self { defs }
    }
}

/// A typed function declaration
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
pub enum TypedGlobalDecls {
    Func(TypedFunctionDeclaration),
    Var(Declaration),
}

/// A typed block of statements
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

/// Declaration represents a declaration statement with the enclosed type and
/// one or more IDs.
#[derive(PartialEq, Debug, Clone)]
pub struct Declaration(pub Type, pub Vec<String>);

/// AstNode representing any allowable statement in the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum TypedStmtNode {
    /// Declaration represents a global declaration statement with the
    /// enclosed string representing the Id of the variable.
    Declaration(Declaration),
    /// Assignment represents an assignment statement of an expressions value
    /// to a given pre-declared assignment.
    /// A block return statement.
    Return(Type, String, Option<TypedExprNode>),
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
    FunctionCall(Type, String, Option<Box<TypedExprNode>>),

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

    // Pointer Operations
    Ref(Type, String),
    Deref(Type, Box<TypedExprNode>),
    ScaleBy(Type, Box<TypedExprNode>),
}

impl Typed for TypedExprNode {
    fn r#type(&self) -> Type {
        match self {
            TypedExprNode::Primary(t, _)
            | TypedExprNode::FunctionCall(t, _, _)
            | TypedExprNode::Equal(t, _, _)
            | TypedExprNode::NotEqual(t, _, _)
            | TypedExprNode::LessThan(t, _, _)
            | TypedExprNode::GreaterThan(t, _, _)
            | TypedExprNode::LessEqual(t, _, _)
            | TypedExprNode::GreaterEqual(t, _, _)
            | TypedExprNode::Subtraction(t, _, _)
            | TypedExprNode::Division(t, _, _)
            | TypedExprNode::Addition(t, _, _)
            | TypedExprNode::Multiplication(t, _, _)
            | TypedExprNode::Ref(t, _)
            | TypedExprNode::Deref(t, _)
            | TypedExprNode::ScaleBy(t, _) => t.clone(),
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
                sign,
                width,
                value: _,
            } => Type::Integer(*sign, *width),
            Primary::Identifier(ty, _) => ty.clone(),
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
    Scale(Type),
    Incompatible,
}

/// Represents an object that contains a representable size in bytes.
pub trait Typed {
    fn r#type(&self) -> Type;
}

/// Marks signed/unsigned integers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Signed {
    Signed,
    Unsigned,
}

/// Represents valid integer bit widths.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum IntegerWidth {
    Eight,
    Sixteen,
    ThirtyTwo,
    SixtyFour,
}

impl ByteSized for IntegerWidth {
    fn size(&self) -> usize {
        match self {
            Self::Eight => 1,
            Self::Sixteen => 2,
            Self::ThirtyTwo => 4,
            Self::SixtyFour => 8,
        }
    }
}

/// A concrete type for function prototypes
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncProto {
    pub return_type: Box<Type>,
    pub args: Vec<Type>,
}

impl FuncProto {
    pub fn new(return_type: Box<Type>, args: Vec<Type>) -> Self {
        Self { return_type, args }
    }
}

/// The size in bytes for a given pointer on the architecture.
const POINTER_BYTE_WIDTH: usize = (usize::BITS / 8) as usize;

/// Represents valid primitive types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Integer(Signed, IntegerWidth),
    Void,
    Func(FuncProto),
    Pointer(Box<Type>),
}

impl ByteSized for Type {
    fn size(&self) -> usize {
        match self {
            Self::Integer(_, iw) => iw.size(),
            Self::Void => 0,
            Self::Func { .. } => POINTER_BYTE_WIDTH,
            Self::Pointer(_) => POINTER_BYTE_WIDTH,
        }
    }
}

impl Type {
    pub fn pointer_to(&self) -> Self {
        Self::Pointer(Box::new(self.clone()))
    }

    pub fn value_at(&self) -> Option<Self> {
        match self {
            Type::Pointer(ty) => Some(*(ty.clone())),
            _ => None,
        }
    }
}

pub trait TypeCompatibility {
    type Output;
    type Rhs;

    fn type_compatible(&self, right: &Self::Rhs, flow_left: bool) -> Self::Output;
}

impl TypeCompatibility for Type {
    type Output = CompatibilityResult;
    type Rhs = Type;

    fn type_compatible(&self, right: &Self::Rhs, flow_left: bool) -> Self::Output {
        match (self, right) {
            (lhs, rhs) if lhs == rhs => CompatibilityResult::Equivalent,
            (Type::Integer(l_sign, l_width), Type::Integer(r_sign, r_width))
                if l_width != r_width && l_sign == r_sign && !flow_left =>
            {
                let widen_to_width = if l_width > r_width { l_width } else { r_width };
                CompatibilityResult::WidenTo(Type::Integer(*l_sign, *widen_to_width))
            }
            (Type::Integer(l_sign, l_width), Type::Integer(r_sign, r_width))
                if l_width >= r_width && l_sign == r_sign && flow_left =>
            {
                let widen_to_width = if l_width > r_width { l_width } else { r_width };
                CompatibilityResult::WidenTo(Type::Integer(*l_sign, *widen_to_width))
            }
            (Type::Pointer(ty), Type::Integer(_, _)) => CompatibilityResult::Scale(*ty.clone()),

            _ => CompatibilityResult::Incompatible,
        }
    }
}