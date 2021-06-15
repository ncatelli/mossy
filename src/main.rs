use mossy::{codegen::CodeGenerationErr, parser};
use scrap::prelude::v1::*;
use std::env;
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::prelude::*;

type RuntimeResult<T> = Result<T, RuntimeError>;

enum RuntimeError {
    FileUnreadable,
    Undefined(String),
}

impl fmt::Debug for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FileUnreadable => write!(f, "source file unreadable"),
            Self::Undefined(s) => write!(f, "{}", s),
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", &self)
    }
}

fn main() {
    let raw_args: Vec<String> = env::args().into_iter().collect::<Vec<String>>();
    let args = raw_args.iter().map(|a| a.as_str()).collect::<Vec<&str>>();

    let cmd = scrap::Cmd::new("mossy")
        .description("An (irresponsibly) experimental C compiler.")
        .author("Nate Catelli <ncatelli@packetfire.org>")
        .version("0.1.0")
        .with_flag(scrap::Flag::expect_string(
            "in-file",
            "i",
            "an input path for a source file.",
        ))
        .with_flag(
            scrap::Flag::expect_string("out-file", "o", "an assembly output path.")
                .optional()
                .with_default("a.s".to_string()),
        )
        .with_handler(|(inf, ouf)| {
            read_src_file(&inf)
                .and_then(|input| compile(&input))
                .and_then(|asm| write_dest_file(&ouf, &asm.as_bytes()))
        });

    let help_string = cmd.help();
    let eval_res = cmd
        .evaluate(&args[..])
        .map_err(|e| RuntimeError::Undefined(e.to_string()))
        .and_then(|flags| cmd.dispatch(flags));

    match eval_res {
        Ok(_) => (),
        Err(_) => println!("{}", &help_string),
    }
}

fn read_src_file(filename: &str) -> RuntimeResult<String> {
    let mut f = File::open(filename).map_err(|_| RuntimeError::FileUnreadable)?;

    let mut contents = String::new();
    match f.read_to_string(&mut contents) {
        Ok(_) => Ok(contents),
        Err(e) => Err(RuntimeError::Undefined(e.to_string())),
    }
}

fn write_dest_file(filename: &str, data: &[u8]) -> RuntimeResult<()> {
    let mut f = OpenOptions::new()
        .truncate(true)
        .create(true)
        .write(true)
        .open(filename)
        .map_err(|_| RuntimeError::FileUnreadable)?;

    match f.write_all(data) {
        Ok(_) => Ok(()),
        Err(e) => Err(RuntimeError::Undefined(e.to_string())),
    }
}

fn compile(source: &str) -> RuntimeResult<String> {
    use mossy::codegen::machine::arch::x86_64;
    use mossy::codegen::CodeGenerator;
    let input: Vec<(usize, char)> = source.chars().enumerate().collect();
    let mut symbol_table = x86_64::SymbolTable::default();

    parser::parse(&input)
        .map_err(|e| RuntimeError::Undefined(format!("{:?}", e)))?
        .into_iter()
        .map(|ast_node| x86_64::X86_64.generate(&mut symbol_table, ast_node))
        .collect::<Result<Vec<Vec<String>>, CodeGenerationErr>>()
        .map(|insts| {
            vec![
                vec![x86_64::codegen_preamble()],
                insts,
                vec![x86_64::codegen_postamble()],
            ]
            .into_iter()
            .flatten()
            .flatten()
            .collect()
        })
        .map(|insts: Vec<String>| insts.into_iter().collect::<String>())
        .map_err(|e| RuntimeError::Undefined(format!("{:?}", e)))
}
