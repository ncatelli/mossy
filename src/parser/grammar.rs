use pest::error::Error;
use pest::Parser;

use crate::ast::{AstNode, BinaryExpr, Number, SpannedAstNode};

pub enum ParseErr {
    Unspecified,
}

impl std::fmt::Debug for ParseErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unspecified => write!(f, "unspecified err"),
        }
    }
}

#[derive(Parser)]
#[grammar = "parser/c.pest"]
pub struct CParser;

pub fn parse<'a>(source: &'a str) -> Result<Vec<Box<SpannedAstNode>>, Error<Rule>> {
    let ast: Vec<Box<SpannedAstNode>> = CParser::parse(Rule::program, source)?
        .into_iter()
        .map(|pair| match pair.as_rule() {
            Rule::expression => Some(Box::new(build_ast_from_expr(pair))),
            _ => None,
        })
        .filter_map(|elem| elem)
        .collect();

    Ok(ast)
}

fn build_ast_from_expr(pair: pest::iterators::Pair<Rule>) -> SpannedAstNode {
    let span = pair.as_span();
    match pair.as_rule() {
        Rule::expression => build_ast_from_expr(pair.into_inner().next().unwrap()),
        Rule::binaryExpr => SpannedAstNode::new(span, parse_binary_expr(pair.into_inner())),
        Rule::integerConstant => build_ast_from_integer_constant(pair),
        unknown_expr => panic!("Unexpected expression: {:?}", unknown_expr),
    }
}

fn parse_binary_expr(pairs: pest::iterators::Pairs<Rule>) -> AstNode {
    let mut pairs = pairs;
    let lhs = pairs.next().map(build_ast_from_expr).unwrap().unwrap();
    let op = pairs.next().unwrap();
    let rhs = pairs.next().map(build_ast_from_expr).unwrap().unwrap();

    AstNode::Expression({
        let lhs = Box::new(lhs);
        let rhs = Box::new(rhs);
        match op.as_str() {
            "+" => BinaryExpr::Plus(lhs, rhs),
            "-" => BinaryExpr::Minus(lhs, rhs),
            "*" => BinaryExpr::Multiply(lhs, rhs),
            "/" => BinaryExpr::Divide(lhs, rhs),
            _ => panic!("Unexpected binary op: {}", op.as_str()),
        }
    })
}

fn build_ast_from_integer_constant(pair: pest::iterators::Pair<Rule>) -> SpannedAstNode {
    match (pair.as_span(), pair.as_rule()) {
        (span, Rule::integerConstant) => {
            let istr = pair.as_str();
            let ui: u64 = istr.parse().unwrap();
            SpannedAstNode::new(span, AstNode::Number(Number(ui)))
        }
        (_, Rule::expression) => build_ast_from_expr(pair),
        unknown_term => panic!("Unexpected term: {:?}", unknown_term),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn should_parse_multi_expression_binary_expression() {
        let input = "5 + 5 - 5 * 5 / 5";
        let ast = super::parse(input);
        println!("{:#?}", &ast);
        assert!(ast.is_ok());
    }
}
