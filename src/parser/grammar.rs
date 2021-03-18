use pest::error::Error;
use pest::Parser;

use crate::ast::{AstNode, BinaryExpr, Number};

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

pub fn parse(source: &str) -> Result<Vec<Box<AstNode>>, Error<Rule>> {
    let ast: Vec<Box<AstNode>> = CParser::parse(Rule::program, source)?
        .into_iter()
        .map(|pair| match pair.as_rule() {
            Rule::expression => Some(Box::new(build_ast_from_expr(pair))),
            _ => None,
        })
        .filter_map(|elem| elem)
        .collect();

    Ok(ast)
}

fn build_ast_from_expr(pair: pest::iterators::Pair<Rule>) -> AstNode {
    match pair.as_rule() {
        Rule::expression => build_ast_from_expr(pair.into_inner().next().unwrap()),
        Rule::binaryExpr => {
            let mut pair = pair.into_inner();
            let lhspair = pair.next().unwrap();
            let lhs = build_ast_from_expr(lhspair);
            let op = pair.next().unwrap();
            let rhspair = pair.next().unwrap();
            let rhs = build_ast_from_expr(rhspair);
            parse_binary_op(op, lhs, rhs)
        }
        Rule::integerConstant => build_ast_from_integer_constant(pair),
        unknown_expr => panic!("Unexpected expression: {:?}", unknown_expr),
    }
}

fn parse_binary_op(pair: pest::iterators::Pair<Rule>, lhs: AstNode, rhs: AstNode) -> AstNode {
    AstNode::Expression({
        let lhs = Box::new(lhs);
        let rhs = Box::new(rhs);
        match pair.as_str() {
            "+" => BinaryExpr::Plus(lhs, rhs),
            "-" => BinaryExpr::Minus(lhs, rhs),
            "*" => BinaryExpr::Multiply(lhs, rhs),
            "/" => BinaryExpr::Divide(lhs, rhs),
            _ => panic!("Unexpected binary op: {}", pair.as_str()),
        }
    })
}

fn build_ast_from_integer_constant(pair: pest::iterators::Pair<Rule>) -> AstNode {
    match pair.as_rule() {
        Rule::integerConstant => {
            let istr = pair.as_str();
            let ui: u64 = istr.parse().unwrap();
            AstNode::Number(Number(ui))
        }
        Rule::expression => build_ast_from_expr(pair),
        unknown_term => panic!("Unexpected term: {:?}", unknown_term),
    }
}
