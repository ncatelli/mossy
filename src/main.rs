use mossy::parser;
use std::env;
use std::fs::{File, OpenOptions};
use std::io::prelude::*;
use std::process;

type RuntimeResult<T> = Result<T, String>;

fn main() {
    let args: Vec<String> = env::args().collect();
    let args_len = args.len();

    match args_len {
        2 => run_file(&args[1]).expect("Unable to open file"),
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
        Ok(_) => compile(contents),
        Err(error) => Err(format!("error: {}", error)),
    }
}

fn write_dest_file(filename: &str, data: &[u8]) -> RuntimeResult<()> {
    let mut f = OpenOptions::new()
        .truncate(true)
        .create(true)
        .write(true)
        .open(filename)
        .map_err(|e| e.to_string())?;

    match f.write_all(data) {
        Ok(_) => Ok(()),
        Err(e) => Err(e.to_string()),
    }
}

fn compile(source: String) -> RuntimeResult<()> {
    let input: Vec<(usize, char)> = source.chars().enumerate().collect();
    parser::parse(&input)
        .map_err(|e| format!("{:?}", e))
        .map(|ast_node| {
            use mossy::codegen::machine::arch::x86_64;
            use mossy::codegen::CodeGenerator;

            x86_64::X86_64.generate(ast_node[0].to_owned())
        })
        .unwrap()
        .map(|insts| {
            let contents = insts.into_iter().collect::<String>();
            write_dest_file("a.s", contents.as_bytes()).unwrap();
        })
        .map_err(|e| format!("{:?}", e))?;

    Ok(())
}
