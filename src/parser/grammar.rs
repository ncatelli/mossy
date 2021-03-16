use crate::ast::{AdditionExpr, DivisionExpr, Expr, Literal, MultiplicationExpr, SubtractionExpr};

peg::parser!(pub grammar parser() for str {
    pub rule expression() -> Expr
        = binary_op()

    rule binary_op() -> Expr = precedence!{
        lhs:@ _ "+" _ rhs:(expression()) { Expr::Addition(AdditionExpr(Box::new(lhs), Box::new(rhs))) }
        lhs:@ _ "-" _ rhs:(expression()) { Expr::Subtraction(SubtractionExpr(Box::new(lhs), Box::new(rhs))) }
        --
        lhs:@ _ "*" _ rhs:(expression()) { Expr::Multiplication(MultiplicationExpr(Box::new(lhs), Box::new(rhs))) }
        lhs:@ _ "/" _ rhs:(expression()) { Expr::Division(DivisionExpr(Box::new(lhs), Box::new(rhs))) }
        --
        l:literal() { l }
    }

    rule literal() -> Expr
        = n:$(['0'..='9']+) {
            let val = std::str::FromStr::from_str(&n.to_owned()).unwrap();
            Expr::Primary(Literal::Int(val))
        }

    rule _() =  quiet!{[' ' | '\t']*}
});
