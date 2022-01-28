use crate::stage::type_check::ast::{self, Declaration, IntegerWidth, Signed};

/// Represents a list of reserved keywords in C.
pub(crate) const RESERVED_KEYWORDS: [&str; 32] = [
    "auto", "void", "char", "short", "int", "long", "float", "double", "sizeof", "struct", "enum",
    "union", "typedef", "register", "extern", "const", "unsigned", "static", "signed", "volatile",
    "switch", "case", "default", "if", "else", "do", "while", "for", "continue", "break", "goto",
    "return",
];

#[derive(Debug)]
pub struct CompilationUnit {
    pub defs: Vec<GlobalDecls>,
}

impl CompilationUnit {
    pub fn new(defs: Vec<GlobalDecls>) -> Self {
        Self { defs }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum GlobalDecls {
    Func(FunctionDeclaration),
    Var(Declaration),
}

/// A new fuction declaration wrapping a string and block.
#[derive(PartialEq, Debug, Clone)]
pub struct Parameter {
    pub id: String,
    pub r#type: ast::Type,
}

impl Parameter {
    pub fn new(id: String, r#type: ast::Type) -> Self {
        Self { id, r#type }
    }
}

/// A new fuction declaration wrapping a string and block.
#[derive(PartialEq, Debug, Clone)]
pub struct FunctionDeclaration {
    pub id: String,
    pub return_type: ast::Type,
    pub params: Vec<Parameter>,
    pub block: CompoundStmts,
}

impl FunctionDeclaration {
    pub fn new(
        id: String,
        return_type: ast::Type,
        params: Vec<Parameter>,
        block: CompoundStmts,
    ) -> Self {
        Self {
            id,
            params,
            return_type,
            block,
        }
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
    /// Declaration represents a declaration statement with the enclosed
    /// strings representing the one or more Ids of the variables of the given
    /// type.
    Declaration(Declaration),
    /// A block return statement.
    Return(Option<ExprNode>),
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
    FunctionCall(String, Option<Box<ExprNode>>),

    /// Assignment represents an assignment statement of an expressions value
    /// to a given pre-declared assignment.
    Assignment(Box<ExprNode>, Box<ExprNode>),

    // Binary Logical
    LogOr(Box<ExprNode>, Box<ExprNode>),
    LogAnd(Box<ExprNode>, Box<ExprNode>),

    // Bitwise
    BitOr(Box<ExprNode>, Box<ExprNode>),
    BitXor(Box<ExprNode>, Box<ExprNode>),
    BitAnd(Box<ExprNode>, Box<ExprNode>),

    // Comparative
    Equal(Box<ExprNode>, Box<ExprNode>),
    NotEqual(Box<ExprNode>, Box<ExprNode>),
    LessThan(Box<ExprNode>, Box<ExprNode>),
    GreaterThan(Box<ExprNode>, Box<ExprNode>),
    LessEqual(Box<ExprNode>, Box<ExprNode>),
    GreaterEqual(Box<ExprNode>, Box<ExprNode>),

    // Bitwise shift
    BitShiftLeft(Box<ExprNode>, Box<ExprNode>),
    BitShiftRight(Box<ExprNode>, Box<ExprNode>),

    // Arithmetic
    Addition(Box<ExprNode>, Box<ExprNode>),
    Subtraction(Box<ExprNode>, Box<ExprNode>),
    Multiplication(Box<ExprNode>, Box<ExprNode>),
    Division(Box<ExprNode>, Box<ExprNode>),
    Modulo(Box<ExprNode>, Box<ExprNode>),

    // Unary
    LogicalNot(Box<ExprNode>),
    Negate(Box<ExprNode>),
    Invert(Box<ExprNode>),

    PreIncrement(Box<ExprNode>),
    PreDecrement(Box<ExprNode>),
    PostIncrement(Box<ExprNode>),
    PostDecrement(Box<ExprNode>),

    // Pointer Operations
    Ref(String),
    Deref(Box<ExprNode>),

    // Array Access
    Index(String, Box<ExprNode>),

    Grouping(Box<ExprNode>),
}

/// Primary represents a primitive type within the ast.
#[derive(PartialEq, Debug, Clone)]
pub enum Primary {
    Integer {
        sign: Signed,
        width: IntegerWidth,
        // value is organized internally as a little-endian value.
        value: [u8; 8],
    },
    Identifier(String),
    Str(Vec<u8>),
}

macro_rules! assignment_expr {
    ($lhs:expr, '=', $rhs:expr) => {
        $crate::parser::ast::ExprNode::Assignment(Box::new($lhs), Box::new($rhs))
    };
}

macro_rules! binary_logical_expr {
    ($lhs:expr, "||", $rhs:expr) => {
        $crate::parser::ast::ExprNode::LogOr(Box::new($lhs), Box::new($rhs))
    };
    ($lhs:expr, "&&", $rhs:expr) => {
        $crate::parser::ast::ExprNode::LogAnd(Box::new($lhs), Box::new($rhs))
    };
}

macro_rules! bitwise_expr {
    ($lhs:expr, "|", $rhs:expr) => {
        $crate::parser::ast::ExprNode::BitOr(Box::new($lhs), Box::new($rhs))
    };
    ($lhs:expr, "^", $rhs:expr) => {
        $crate::parser::ast::ExprNode::BitXor(Box::new($lhs), Box::new($rhs))
    };
    ($lhs:expr, "&", $rhs:expr) => {
        $crate::parser::ast::ExprNode::BitAnd(Box::new($lhs), Box::new($rhs))
    };
}

macro_rules! equality_expr {
    ($lhs:expr, "==", $rhs:expr) => {
        $crate::parser::ast::ExprNode::Equal(Box::new($lhs), Box::new($rhs))
    };
    ($lhs:expr, "!=", $rhs:expr) => {
        $crate::parser::ast::ExprNode::NotEqual(Box::new($lhs), Box::new($rhs))
    };
}

macro_rules! bitwise_shift_expr {
    ($lhs:expr, "<<", $rhs:expr) => {
        $crate::parser::ast::ExprNode::BitShiftLeft(Box::new($lhs), Box::new($rhs))
    };
    ($lhs:expr, ">>", $rhs:expr) => {
        $crate::parser::ast::ExprNode::BitShiftRight(Box::new($lhs), Box::new($rhs))
    };
}

macro_rules! term_expr {
    ($lhs:expr, '+', $rhs:expr) => {
        $crate::parser::ast::ExprNode::Addition(Box::new($lhs), Box::new($rhs))
    };
    ($lhs:expr, '-', $rhs:expr) => {
        $crate::parser::ast::ExprNode::Subtraction(Box::new($lhs), Box::new($rhs))
    };
}

macro_rules! factor_expr {
    ($lhs:expr, '*', $rhs:expr) => {
        $crate::parser::ast::ExprNode::Multiplication(Box::new($lhs), Box::new($rhs))
    };
    ($lhs:expr, '/', $rhs:expr) => {
        $crate::parser::ast::ExprNode::Division(Box::new($lhs), Box::new($rhs))
    };
    ($lhs:expr, '%', $rhs:expr) => {
        $crate::parser::ast::ExprNode::Modulo(Box::new($lhs), Box::new($rhs))
    };
}

#[allow(unused)]
macro_rules! primary_expr {
    (i8 $value:expr) => {
        $crate::parser::ast::ExprNode::Primary(crate::parser::ast::Primary::Integer {
            sign: $crate::stage::type_check::ast::Signed::Signed,
            width: $crate::stage::type_check::ast::IntegerWidth::Eight,
            value: $crate::util::pad_to_64bit_array(($value as i8).to_le_bytes()),
        })
    };
    (u8 $value:expr) => {
        $crate::parser::ast::ExprNode::Primary(crate::parser::ast::Primary::Integer {
            sign: $crate::stage::type_check::ast::Signed::Unsigned,
            width: $crate::stage::type_check::ast::IntegerWidth::Eight,
            value: $crate::util::pad_to_64bit_array(($value as u8).to_le_bytes()),
        })
    };

    (i16 $value:expr) => {
        $crate::parser::ast::ExprNode::Primary(crate::parser::ast::Primary::Integer {
            sign: $crate::stage::type_check::ast::Signed::Signed,
            width: $crate::stage::type_check::ast::IntegerWidth::Sixteen,
            value: $crate::util::pad_to_64bit_array(($value as i16).to_le_bytes()),
        })
    };
    (u16 $value:expr) => {
        $crate::parser::ast::ExprNode::Primary(crate::parser::ast::Primary::Integer {
            sign: $crate::stage::type_check::ast::Signed::Unsigned,
            width: $crate::stage::type_check::ast::IntegerWidth::Sixteen,
            value: $crate::util::pad_to_64bit_array(($value as u16).to_le_bytes()),
        })
    };

    (i32 $value:expr) => {
        $crate::parser::ast::ExprNode::Primary(crate::parser::ast::Primary::Integer {
            sign: $crate::stage::type_check::ast::Signed::Signed,
            width: $crate::stage::type_check::ast::IntegerWidth::ThirtyTwo,
            value: $crate::util::pad_to_64bit_array(($value as i32).to_le_bytes()),
        })
    };
    (u32 $value:expr) => {
        $crate::parser::ast::ExprNode::Primary(crate::parser::ast::Primary::Integer {
            sign: $crate::stage::type_check::ast::Signed::Unsigned,
            width: $crate::stage::type_check::ast::IntegerWidth::ThirtyTwo,
            value: $crate::util::pad_to_64bit_array(($value as u32).to_le_bytes()),
        })
    };

    (i64 $value:expr) => {
        $crate::parser::ast::ExprNode::Primary(crate::parser::ast::Primary::Integer {
            sign: $crate::stage::type_check::ast::Signed::Signed,
            width: $crate::stage::type_check::ast::IntegerWidth::SixtyFour,
            value: $crate::util::pad_to_64bit_array(($value as i64).to_le_bytes()),
        })
    };
    (u64 $value:expr) => {
        $crate::parser::ast::ExprNode::Primary(crate::parser::ast::Primary::Integer {
            sign: $crate::stage::type_check::ast::Signed::Unsigned,
            width: $crate::stage::type_check::ast::IntegerWidth::SixtyFour,
            value: $crate::util::pad_to_64bit_array(($value as u64).to_le_bytes()),
        })
    };

    (str $value:expr) => {
        $crate::parser::ast::ExprNode::Primary(crate::parser::ast::Primary::Str(
            $value.chars().map(|c| c as u8).collect(),
        ))
    };
}

macro_rules! grouping_expr {
    ($value:expr) => {
        $crate::parser::ast::ExprNode::Grouping(Box::new($value))
    };
}
