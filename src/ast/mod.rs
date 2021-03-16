mod interpret;

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Addition(AdditionExpr),
    Subtraction(SubtractionExpr),
    Multiplication(MultiplicationExpr),
    Division(DivisionExpr),
    Primary(Literal),
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct AdditionExpr(pub Box<Expr>, pub Box<Expr>);

impl std::fmt::Display for AdditionExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(+ {} {})", self.0, self.1)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct SubtractionExpr(pub Box<Expr>, pub Box<Expr>);

impl std::fmt::Display for SubtractionExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(- {} {})", self.0, self.1)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct MultiplicationExpr(pub Box<Expr>, pub Box<Expr>);

impl std::fmt::Display for MultiplicationExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(* {} {})", self.0, self.1)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct DivisionExpr(pub Box<Expr>, pub Box<Expr>);

impl std::fmt::Display for DivisionExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(/ {} {})", self.0, self.1)
    }
}

/// A literal value in the typesystem.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Literal {
    Int(u64),
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(val) => write!(f, "{}", val),
        }
    }
}
