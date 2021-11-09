pub type Span = std::ops::Range<usize>;

#[derive(PartialEq, Debug, Clone)]
pub struct FunctionDeclaration {
    pub id: String,
    pub block: CompoundStmts,
}

impl FunctionDeclaration {
    pub fn new(id: String, block: CompoundStmts) -> Self {
        Self { id, block }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct CompoundStmts {
    inner: Vec<StmtNode>,
}

impl CompoundStmts {
    pub fn new(inner: Vec<StmtNode>) -> Self {
        Self { inner }
    }
}

impl From<CompoundStmts> for Vec<StmtNode> {
    fn from(src: CompoundStmts) -> Self {
        src.inner
    }
}

/// AstNode representing any allowable statement in the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum StmtNode {
    /// Declaration represents a global declaration statement with the
    /// enclosed string representing the Id of the variable.
    Declaration(Kind, String),
    /// Assignment represents an assignment statement of an expressions value
    /// to a given pre-declared assignment.
    Assignment(String, ExprNode),
    /// Represents a statement containing only a single expression.
    Expression(ExprNode),
    /// Represents a conditional if statement with an optional else clause.
    If(ExprNode, CompoundStmts, Option<CompoundStmts>),
    /// Represents a while loop.
    While(ExprNode, CompoundStmts),
    For(Box<StmtNode>, ExprNode, Box<StmtNode>, CompoundStmts),
}

/// Represents a single expression in the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum ExprNode {
    Primary(Kind, Primary),

    // Comparative
    Equal(Kind, Box<ExprNode>, Box<ExprNode>),
    NotEqual(Kind, Box<ExprNode>, Box<ExprNode>),
    LessThan(Kind, Box<ExprNode>, Box<ExprNode>),
    GreaterThan(Kind, Box<ExprNode>, Box<ExprNode>),
    LessEqual(Kind, Box<ExprNode>, Box<ExprNode>),
    GreaterEqual(Kind, Box<ExprNode>, Box<ExprNode>),

    // Arithmetic
    Subtraction(Kind, Box<ExprNode>, Box<ExprNode>),
    Division(Kind, Box<ExprNode>, Box<ExprNode>),
    Addition(Kind, Box<ExprNode>, Box<ExprNode>),
    Multiplication(Kind, Box<ExprNode>, Box<ExprNode>),
}

/// Primary represents a primitive type within the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum Primary {
    Uint8(Uint8),
    Identifier(Option<Kind>, String),
}

impl Kinded for Primary {
    fn kind(&self) -> Kind {
        match self {
            Primary::Uint8(_) => Kind::Uint8,
            Primary::Identifier(Some(kind), _) => *kind,
            Primary::Identifier(None, id) => panic!("unidentified variable: {}", id),
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

impl Kinded for Uint8 {
    fn kind(&self) -> Kind {
        Kind::Uint8
    }
}

/// Represents an object that contains a representable size in bytes.
pub trait ByteSized {
    fn size(&self) -> usize;
}

pub enum CompatibilityResult {
    Equivalent,
    WidenTo(Kind),
    Incompatible,
}

/// Represents an object that contains a representable size in bytes.
pub trait Kinded {
    fn kind(&self) -> Kind;
}

/// Represents valid primitive types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Uint8,
    Char,
    Void,
}

impl ByteSized for Kind {
    fn size(&self) -> usize {
        match self {
            Kind::Uint8 | Kind::Char => 1,
            Kind::Void => 0,
        }
    }
}

pub(crate) fn type_compatible(left: Kind, right: Kind, flow_left: bool) -> CompatibilityResult {
    match (left, right) {
        _ if left == right => CompatibilityResult::Equivalent,
        (Kind::Uint8, Kind::Char) => CompatibilityResult::WidenTo(Kind::Uint8),
        (Kind::Char, Kind::Uint8) if !flow_left => CompatibilityResult::WidenTo(Kind::Uint8),
        _ => CompatibilityResult::Incompatible,
    }
}
