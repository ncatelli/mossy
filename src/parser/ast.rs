use crate::ast::{IntegerWidth, Signed};

pub type Span = core::ops::Range<usize>;

#[derive(Debug)]
pub struct Program {
    pub defs: Vec<FunctionDeclaration>,
}

impl Program {
    pub fn new(defs: Vec<FunctionDeclaration>) -> Self {
        Self { defs }
    }
}

/// A new fuction declaration wrapping a string and block.
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

/// A compound block of statements.
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
    Declaration(crate::ast::Type, String),
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
    Primary(Primary),
    FuncCall(String, Box<ExprNode>),

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
    Integer {
        sign: Signed,
        width: IntegerWidth,
        value: u64,
    },
    Identifier(String),
}
