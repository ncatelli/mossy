use parcel::prelude::v1::*;
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::process;

mod ast;
mod parser;

type RuntimeResult<T> = Result<T, String>;

fn main() {
    let args: Vec<String> = env::args().collect();
    let args_len = args.len();

    match args_len {
        2 => run_file(&args[1]).expect("Unable to parse file"),
        _ => {
            println!("Usage: mossy [script]");
            process::exit(64);
        }
    }
}

fn run_file(filename: &str) -> Result<(), String> {
    let mut f = File::open(filename).expect("file not found");

    let mut contents = String::new();
    match f.read_to_string(&mut contents) {
        Ok(_) => {
            compile(contents).unwrap();
            Ok(())
        }
        Err(error) => Err(format!("error: {}", error)),
    }
}

fn compile(source: String) -> RuntimeResult<()> {
    let input: Vec<char> = source.chars().into_iter().collect();
    let astnode = parser::expression()
        .parse(&input)
        .expect("unsuccessful parse")
        .unwrap();
    println!("{:?}", ast::interpret::interpret(astnode));
    Ok(())
}
