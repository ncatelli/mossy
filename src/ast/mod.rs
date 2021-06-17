pub type Span = std::ops::Range<usize>;

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
    Declaration(String),
    /// Assignment represents an assignment statement of an expressions value
    /// to a given pre-declared assignment.
    Assignment(String, ExprNode),
    /// Represents a statement containing only a single expression.
    Expression(ExprNode),
    If(ExprNode, CompoundStmts, Option<CompoundStmts>),
}

/// Represents a single expression in the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum ExprNode {
    Primary(Primary),

    // Comparative
    Equal(Box<ExprNode>, Box<ExprNode>),
    NotEqual(Box<ExprNode>, Box<ExprNode>),
    LessThan(Box<ExprNode>, Box<ExprNode>),
    GreaterThan(Box<ExprNode>, Box<ExprNode>),
    LessEqual(Box<ExprNode>, Box<ExprNode>),
    GreaterEqual(Box<ExprNode>, Box<ExprNode>),

    // Arithmetic
    Subtraction(Box<ExprNode>, Box<ExprNode>),
    Division(Box<ExprNode>, Box<ExprNode>),
    Addition(Box<ExprNode>, Box<ExprNode>),
    Multiplication(Box<ExprNode>, Box<ExprNode>),
}

/// Primary represents a primitive type within the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum Primary {
    Uint8(Uint8),
    Identifier(String),
}

/// represents an 8-bit unsigned integer.
#[derive(PartialEq, Debug, Clone)]
pub struct Uint8(pub u8);

impl std::fmt::Display for Uint8 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
