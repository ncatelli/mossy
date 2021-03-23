pub mod interpret;

pub type Span = std::ops::Range<usize>;

#[derive(PartialEq, Debug, Clone)]
pub struct SpannedExprNode {
    pub span: Span,
    pub node: ExprNode,
}

impl<'a> SpannedExprNode {
    pub fn new(span: Span, node: ExprNode) -> Self {
        Self { span, node }
    }

    pub fn unwrap(self) -> ExprNode {
        self.node
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprNode {
    Number(Number),
    Subtraction(Box<ExprNode>, Box<ExprNode>),
    Division(Box<ExprNode>, Box<ExprNode>),
    Addition(Box<ExprNode>, Box<ExprNode>),
    Multiplication(Box<ExprNode>, Box<ExprNode>),
}

#[derive(PartialEq, Debug, Clone)]
pub struct Number(pub u64);
