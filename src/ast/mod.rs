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
    Equal(EqualExprNode),
    NotEqual(NotEqualExprNode),
    LessThan(LessThanExprNode),
    GreaterThan(GreaterThanExprNode),
    LessEqual(LessEqualExprNode),
    GreaterEqual(GreaterEqualExprNode),

    // Arithmetic
    Subtraction(SubtractionExprNode),
    Division(DivisionExprNode),
    Addition(AdditionExprNode),
    Multiplication(MultiplicationExprNode),
}

/// Functions as a marker trait to denote that the implementing type is one of
/// the Comparative branch of expressions.
pub trait ComparativeExpression {}

// Concrete comparative expression

macro_rules! generate_comparative_nodes {
    ($($name:tt,)*) => {
       $(
            #[derive(Debug, Clone, PartialEq)]
            pub struct $name {
                pub lhs: Box<ExprNode>,
                pub rhs: Box<ExprNode>,
            }

            impl ComparativeExpression for $name {}

            impl $name {
                pub(crate) fn new(lhs: Box<ExprNode>, rhs: Box<ExprNode>) -> Self {
                    Self { lhs, rhs }
                }
            }
       )*
    };
}

generate_comparative_nodes! {
    EqualExprNode,
    NotEqualExprNode,
    LessThanExprNode,
    GreaterThanExprNode,
    LessEqualExprNode,
    GreaterEqualExprNode,
}

/// Functions as a marker trait to denote that the implementing type is one of
/// the Arithmetic branch of expressions.
pub trait ArithmeticExpression {}

// Concrete Arithmetic expression

macro_rules! generate_arithmetic_nodes {
    ($($name:tt,)*) => {
       $(
            #[derive(Debug, Clone, PartialEq)]
            pub struct $name {
                pub lhs: Box<ExprNode>,
                pub rhs: Box<ExprNode>,
            }

            impl ArithmeticExpression for $name {}

            impl $name {
                pub(crate) fn new(lhs: Box<ExprNode>, rhs: Box<ExprNode>) -> Self {
                    Self { lhs, rhs }
                }
            }
       )*
    };
}

generate_arithmetic_nodes! {
    AdditionExprNode,
    SubtractionExprNode,
    MultiplicationExprNode,
    DivisionExprNode,
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
