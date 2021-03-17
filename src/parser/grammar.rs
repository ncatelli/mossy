use self::AstNode::*;
use pest::error::Error;
use pest::Parser;

use crate::ast::{AstNode, BinaryVerb, UnaryVerb};

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
        Rule::unaryExpr => {
            let mut pair = pair.into_inner();
            let verb = pair.next().unwrap();
            let expr = pair.next().unwrap();
            let expr = build_ast_from_expr(expr);
            parse_unary_verb(verb, expr)
        }
        Rule::binaryExpr => {
            let mut pair = pair.into_inner();
            let lhspair = pair.next().unwrap();
            let lhs = build_ast_from_expr(lhspair);
            let verb = pair.next().unwrap();
            let rhspair = pair.next().unwrap();
            let rhs = build_ast_from_expr(rhspair);
            parse_binary_verb(verb, lhs, rhs)
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
        Rule::string => {
            let str = &pair.as_str();
            // Strip leading and ending quotes.
            let str = &str[1..str.len() - 1];
            // Escaped string quotes become single quotes here.
            let str = str.replace("''", "'");
            AstNode::Str(str.to_string())
        }
        unknown_expr => panic!("Unexpected expression: {:?}", unknown_expr),
    }
}

fn parse_binary_verb(pair: pest::iterators::Pair<Rule>, lhs: AstNode, rhs: AstNode) -> AstNode {
    AstNode::BinaryOp {
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        verb: match pair.as_str() {
            "+" => BinaryVerb::Plus,
            "-" => BinaryVerb::Minus,
            "*" => BinaryVerb::Multiply,
            "/" => BinaryVerb::Divide,
            "<" => BinaryVerb::LessThan,
            "<=" => BinaryVerb::LessOrEqual,
            ">" => BinaryVerb::GreaterThan,
            ">=" => BinaryVerb::GreaterOrEqual,
            "=" => BinaryVerb::Equal,
            _ => panic!("Unexpected binary verb: {}", pair.as_str()),
        },
    }
}

fn parse_unary_verb(pair: pest::iterators::Pair<Rule>, expr: AstNode) -> AstNode {
    AstNode::UnaryOp {
        verb: match pair.as_str() {
            ">:" => UnaryVerb::Increment,
            "*:" => UnaryVerb::Square,
            "-" => UnaryVerb::Negate,
            "%" => UnaryVerb::Reciprocal,
            "#" => UnaryVerb::Tally,
            ">." => UnaryVerb::Ceiling,
            "$" => UnaryVerb::ShapeOf,
            _ => panic!("Unsupported unary verb: {}", pair.as_str()),
        },
        expr: Box::new(expr),
    }
}

fn build_ast_from_term(pair: pest::iterators::Pair<Rule>) -> AstNode {
    match pair.as_rule() {
        Rule::integer => {
            let istr = pair.as_str();
            match (&istr[..1], istr) {
                ("-", unparsed) => {
                    let si: i64 = unparsed.parse().unwrap();
                    AstNode::SignedInteger(si)
                }
                (_, unparsed) => {
                    let ui: u64 = unparsed.parse().unwrap();
                    AstNode::UnsignedInteger(ui)
                }
            }
        }
        Rule::decimal => {
            let dstr = pair.as_str();
            let (sign, dstr) = match &dstr[..1] {
                "-" => (-1.0, &dstr[1..]),
                _ => (1.0, &dstr[..]),
            };
            let mut flt: f64 = dstr.parse().unwrap();
            if flt != 0.0 {
                // Avoid negative zeroes; only multiply sign by nonzeroes.
                flt *= sign;
            }
            AstNode::DoublePrecisionFloat(flt)
        }
        Rule::expr => build_ast_from_expr(pair),
        unknown_term => panic!("Unexpected term: {:?}", unknown_term),
    }
}
