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
    Expression(BinaryExpr),
    Number(Number),
}

#[derive(PartialEq, Debug, Clone)]
pub struct Number(pub u64);
