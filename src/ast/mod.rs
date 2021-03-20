pub mod interpret;

#[derive(PartialEq, Debug, Clone)]
pub struct SpannedAstNode<'a> {
    pub span: pest::Span<'a>,
    pub node: AstNode,
}

impl<'a> SpannedAstNode<'a> {
    pub fn new(span: pest::Span<'a>, node: AstNode) -> Self {
        Self { span, node }
    }

    pub fn unwrap(self) -> AstNode {
        self.node
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum AstNode {
    Expression(BinaryExpr),
    Number(Number),
}

#[derive(PartialEq, Debug, Clone)]
pub enum BinaryExpr {
    Minus(Box<AstNode>, Box<AstNode>),
    Divide(Box<AstNode>, Box<AstNode>),
    Plus(Box<AstNode>, Box<AstNode>),
    Multiply(Box<AstNode>, Box<AstNode>),
}

#[derive(PartialEq, Debug, Clone)]
pub struct Number(pub u64);
