pub mod interpret;

pub type Span = std::ops::Range<usize>;

#[derive(PartialEq, Debug, Clone)]
pub struct SpannedExprNode {
    pub span: Span,
    pub node: ExprNode,
}

impl<'a> SpannedExprNode {
    #[allow(dead_code)]
    pub fn new(span: Span, node: ExprNode) -> Self {
        Self { span, node }
    }

    #[allow(dead_code)]
    pub fn unwrap(self) -> ExprNode {
        self.node
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum StmtNode {
    Expression(ExprNode),
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprNode {
    Primary(Primary),
    Subtraction(Box<ExprNode>, Box<ExprNode>),
    Division(Box<ExprNode>, Box<ExprNode>),
    Addition(Box<ExprNode>, Box<ExprNode>),
    Multiplication(Box<ExprNode>, Box<ExprNode>),
}

#[derive(PartialEq, Debug, Clone)]
pub enum Primary {
    Uint8(Uint8),
}

#[derive(PartialEq, Debug, Clone)]
pub struct Uint8(pub u8);

impl std::fmt::Display for Uint8 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
