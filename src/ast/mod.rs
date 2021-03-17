pub mod interpret;
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum UnaryVerb {
    Increment,
    Square,
    Negate,
    Reciprocal,
    Tally,
    Ceiling,
    ShapeOf,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum BinaryVerb {
    Minus,
    Divide,
    Plus,
    Multiply,
    LessThan,
    LessOrEqual,
    GreaterThan,
    GreaterOrEqual,
    Equal,
}

#[derive(PartialEq, Debug, Clone)]
pub enum AstNode {
    UnsignedInteger(u64),
    SignedInteger(i64),
    DoublePrecisionFloat(f64),
    UnaryOp {
        verb: UnaryVerb,
        expr: Box<AstNode>,
    },
    BinaryOp {
        verb: BinaryVerb,
        lhs: Box<AstNode>,
        rhs: Box<AstNode>,
    },
    Terms(Vec<AstNode>),
    Str(String),
}
