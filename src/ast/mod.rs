pub mod interpret;

#[derive(PartialEq, Debug, Clone)]
pub enum BinaryExpr {
    Minus(Box<AstNode>, Box<AstNode>),
    Divide(Box<AstNode>, Box<AstNode>),
    Plus(Box<AstNode>, Box<AstNode>),
    Multiply(Box<AstNode>, Box<AstNode>),
}

#[derive(PartialEq, Debug, Clone)]
pub enum AstNode {
    Literal(Literal),
    BinaryExpr(BinaryExpr),
    Terms(Vec<AstNode>),
}

#[derive(PartialEq, Debug, Clone)]
pub enum Literal {
    UnsignedInteger(u64),
}
