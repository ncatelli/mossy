use self::AstNode::*;
use pest::error::Error;
use pest::Parser;

use crate::ast::{AstNode, BinaryExpr, Literal};

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
            Rule::expr => Some(Box::new(build_ast_from_expr(pair))),
            _ => None,
        })
        .filter_map(|elem| elem)
        .collect();

    Ok(ast)
}

fn build_ast_from_expr(pair: pest::iterators::Pair<Rule>) -> AstNode {
    match pair.as_rule() {
        Rule::expr => build_ast_from_expr(pair.into_inner().next().unwrap()),
        Rule::binaryExpr => {
            let mut pair = pair.into_inner();
            let lhspair = pair.next().unwrap();
            let lhs = build_ast_from_expr(lhspair);
            let verb = pair.next().unwrap();
            let rhspair = pair.next().unwrap();
            let rhs = build_ast_from_expr(rhspair);
            parse_binary_op(verb, lhs, rhs)
        }
        Rule::terms => {
            let terms: Vec<AstNode> = pair.into_inner().map(build_ast_from_term).collect();
            // If there's just a single term, return it without
            // wrapping it in a Terms node.
            match terms.len() {
                1 => terms.get(0).unwrap().clone(),
                _ => Terms(terms),
            }
        }
        unknown_expr => panic!("Unexpected expression: {:?}", unknown_expr),
    }
}

fn parse_binary_op(pair: pest::iterators::Pair<Rule>, lhs: AstNode, rhs: AstNode) -> AstNode {
    AstNode::BinaryExpr({
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

fn build_ast_from_term(pair: pest::iterators::Pair<Rule>) -> AstNode {
    match pair.as_rule() {
        Rule::integer => {
            let istr = pair.as_str();
            let ui: u64 = istr.parse().unwrap();
            AstNode::Literal(Literal::UnsignedInteger(ui))
        }
        Rule::expr => build_ast_from_expr(pair),
        unknown_term => panic!("Unexpected term: {:?}", unknown_term),
    }
}
