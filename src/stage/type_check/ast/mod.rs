macro_rules! generate_type_specifier {
    (integer, $sign:expr, $width:expr) => {
        $crate::stage::type_check::ast::Type::Integer($sign, $width)
    };
    (char) => {
        generate_type_specifier!(i8)
    };
    (ptr => $ty:expr) => {
        $crate::stage::type_check::ast::Type::Pointer(Box::new($ty))
    };
    (i8) => {
        generate_type_specifier!(
            integer,
            $crate::stage::type_check::ast::Signed::Signed,
            $crate::stage::type_check::ast::IntegerWidth::Eight
        )
    };
    (u8) => {
        generate_type_specifier!(
            integer,
            $crate::stage::type_check::ast::Signed::Unsigned,
            $crate::stage::type_check::ast::IntegerWidth::Eight
        )
    };
    (i16) => {
        generate_type_specifier!(
            integer,
            $crate::stage::type_check::ast::Signed::Signed,
            $crate::stage::type_check::ast::IntegerWidth::Sixteen
        )
    };
    (i32) => {
        generate_type_specifier!(
            integer,
            $crate::stage::type_check::ast::Signed::Signed,
            $crate::stage::type_check::ast::IntegerWidth::ThirtyTwo
        )
    };
    (u32) => {
        generate_type_specifier!(
            integer,
            $crate::stage::type_check::ast::Signed::Unsigned,
            $crate::stage::type_check::ast::IntegerWidth::ThirtyTwo
        )
    };
    (i64) => {
        generate_type_specifier!(
            integer,
            $crate::stage::type_check::ast::Signed::Signed,
            $crate::stage::type_check::ast::IntegerWidth::SixtyFour
        )
    };
    (u64) => {
        generate_type_specifier!(
            integer,
            $crate::stage::type_check::ast::Signed::Unsigned,
            $crate::stage::type_check::ast::IntegerWidth::SixtyFour
        )
    };
}

#[derive(Debug)]
pub struct TypedProgram {
    pub defs: Vec<TypedGlobalDecls>,
}

impl TypedProgram {
    pub fn new(defs: Vec<TypedGlobalDecls>) -> Self {
        Self { defs }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    pub id: String,
    pub r#type: Type,
}

impl Parameter {
    pub fn new(id: String, r#type: Type) -> Self {
        Self { id, r#type }
    }
}

/// A typed function declaration
#[derive(PartialEq, Debug, Clone)]
pub struct TypedFunctionDeclaration {
    pub id: String,
    pub block: TypedCompoundStmts,
    pub parameters: Vec<Type>,
    local_vars: Vec<(Type, usize)>,
}

impl TypedFunctionDeclaration {
    pub fn new(
        id: String,
        block: TypedCompoundStmts,
        parameters: Vec<Type>,
        local_vars: Vec<(Type, usize)>,
    ) -> Self {
        Self {
            id,
            block,
            parameters,
            local_vars,
        }
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
pub enum Declaration {
    Scalar(Type, Vec<String>),
    Array { ty: Type, id: String, size: usize },
}

/// AstNode representing any allowable statement in the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum TypedStmtNode {
    /// Declaration represents a local declaration statement with the
    /// enclosed string representing the Id of the variable and it's local
    /// stack offset.
    LocalDeclaration(Declaration, Vec<usize>),
    /// Assignment represents an assignment statement of an expressions value
    /// to a given pre-declared assignment.
    /// A block return statement.
    Return(Type, String, Option<TypedExprNode>),
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

/// Represents whether an identifier is locally stored on the stack or
/// globally behind a label.
#[derive(PartialEq, Debug, Clone)]
pub enum IdentifierLocality {
    Global(String),
    Local(usize),
    Parameter(usize),
}

/// Represents a single expression in the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum TypedExprNode {
    Primary(Type, Primary),
    FunctionCall(Type, String, Vec<TypedExprNode>),

    IdentifierAssignment(Type, IdentifierLocality, Box<TypedExprNode>),
    DerefAssignment(Type, Box<TypedExprNode>, Box<TypedExprNode>),

    // Binary Logical
    LogOr(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    LogAnd(Type, Box<TypedExprNode>, Box<TypedExprNode>),

    // Bitwise
    BitOr(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    BitXor(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    BitAnd(Type, Box<TypedExprNode>, Box<TypedExprNode>),

    // Comparative
    Equal(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    NotEqual(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    LessThan(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    GreaterThan(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    LessEqual(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    GreaterEqual(Type, Box<TypedExprNode>, Box<TypedExprNode>),

    // Bitwise shift
    BitShiftLeft(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    BitShiftRight(Type, Box<TypedExprNode>, Box<TypedExprNode>),

    // Arithmetic
    Addition(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    Subtraction(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    Division(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    Modulo(Type, Box<TypedExprNode>, Box<TypedExprNode>),
    Multiplication(Type, Box<TypedExprNode>, Box<TypedExprNode>),

    // Unary
    LogicalNot(Type, Box<TypedExprNode>),
    Negate(Type, Box<TypedExprNode>),
    Invert(Type, Box<TypedExprNode>),

    PreIncrement(Type, Box<TypedExprNode>),
    PreDecrement(Type, Box<TypedExprNode>),
    PostIncrement(Type, Box<TypedExprNode>),
    PostDecrement(Type, Box<TypedExprNode>),

    // Pointer Operations
    Ref(Type, IdentifierLocality),
    Deref(Type, Box<TypedExprNode>),
    ScaleBy(Type, Box<TypedExprNode>),

    Grouping(Type, Box<TypedExprNode>),
}

impl Typed for TypedExprNode {
    fn r#type(&self) -> Type {
        match self {
            TypedExprNode::Primary(ty, _)
            | TypedExprNode::FunctionCall(ty, _, _)
            | TypedExprNode::IdentifierAssignment(ty, _, _)
            | TypedExprNode::DerefAssignment(ty, _, _)
            | TypedExprNode::BitOr(ty, _, _)
            | TypedExprNode::BitXor(ty, _, _)
            | TypedExprNode::BitAnd(ty, _, _)
            | TypedExprNode::BitShiftLeft(ty, _, _)
            | TypedExprNode::BitShiftRight(ty, _, _)
            | TypedExprNode::Addition(ty, _, _)
            | TypedExprNode::Subtraction(ty, _, _)
            | TypedExprNode::Division(ty, _, _)
            | TypedExprNode::Multiplication(ty, _, _)
            | TypedExprNode::Modulo(ty, _, _)
            | TypedExprNode::LogicalNot(ty, _)
            | TypedExprNode::Negate(ty, _)
            | TypedExprNode::Invert(ty, _)
            | TypedExprNode::PreIncrement(ty, _)
            | TypedExprNode::PreDecrement(ty, _)
            | TypedExprNode::PostIncrement(ty, _)
            | TypedExprNode::PostDecrement(ty, _)
            | TypedExprNode::Ref(ty, _)
            | TypedExprNode::Deref(ty, _)
            | TypedExprNode::ScaleBy(ty, _)
            | TypedExprNode::Grouping(ty, _) => ty.clone(),
            // Boolean types
            TypedExprNode::LogOr(_, _, _)
            | TypedExprNode::LogAnd(_, _, _)
            | TypedExprNode::Equal(_, _, _)
            | TypedExprNode::NotEqual(_, _, _)
            | TypedExprNode::LessThan(_, _, _)
            | TypedExprNode::GreaterThan(_, _, _)
            | TypedExprNode::LessEqual(_, _, _)
            | TypedExprNode::GreaterEqual(_, _, _) => {
                Type::Integer(Signed::Unsigned, IntegerWidth::One)
            }
        }
    }
}

/// Primary represents a primitive type within the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum Primary {
    Integer {
        sign: Signed,
        width: IntegerWidth,
        value: [u8; 8],
    },
    Identifier(Type, IdentifierLocality),
    Str(Vec<u8>),
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
            Primary::Str(_) => {
                generate_type_specifier!(ptr => generate_type_specifier!(char))
            }
        }
    }
}

/// Represents an object that contains a representable size in bytes.
pub trait ByteSized {
    fn size(&self) -> usize;
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
    One,
    Eight,
    Sixteen,
    ThirtyTwo,
    SixtyFour,
}

impl ByteSized for IntegerWidth {
    fn size(&self) -> usize {
        match self {
            Self::One | Self::Eight => 1,
            Self::Sixteen => 2,
            Self::ThirtyTwo => 4,
            Self::SixtyFour => 8,
        }
    }
}

/// A concrete type for function prototypes
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionSignature {
    pub return_type: Box<Type>,
    pub parameters: Vec<Parameter>,
}

impl FunctionSignature {
    pub fn new(return_type: Box<Type>, parameters: Vec<Parameter>) -> Self {
        Self {
            return_type,
            parameters,
        }
    }
}

/// The size in bytes for a given pointer on the architecture.
const POINTER_BYTE_WIDTH: usize = (usize::BITS / 8) as usize;

/// Represents valid primitive types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Integer(Signed, IntegerWidth),
    Void,
    Func(FunctionSignature),
    Pointer(Box<Type>),
}

impl ByteSized for Type {
    fn size(&self) -> usize {
        (&self).size()
    }
}

impl ByteSized for &Type {
    fn size(&self) -> usize {
        match self {
            Type::Integer(_, iw) => iw.size(),
            Type::Void => 0,
            Type::Func { .. } => POINTER_BYTE_WIDTH,
            Type::Pointer(_) => POINTER_BYTE_WIDTH,
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
