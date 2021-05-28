use mossy::{codegen::CodeGenerationErr, parser};
use scrap::prelude::v1::*;
use std::env;
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::prelude::*;

const EXIT_SUCCESS: i32 = 0;

const ROOT_HELP_STRING: &str = "Usage: mossy [OPTIONS]
An (irresponsibly) experimental C compiler.

Flags:
    --help, -h          print help string
    --version, -v       
    --in-file, -i       an input source file.
    --out-file, -o      an output path assembly

Subcommands:   
";

type RuntimeResult<T> = Result<T, RuntimeError>;

enum RuntimeError {
    InvalidArguments(String),
    FileUnreadable,
    Undefined(String),
}

impl fmt::Debug for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidArguments(hs) => write!(f, "{}", hs),
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
    let args: Vec<String> = env::args().collect();

    let res = Cmd::new()
        .name("mossy")
        .description("An (irresponsibly) experimental C compiler.")
        .author("Nate Catelli <ncatelli@packetfire.org>")
        .version("0.1.0")
        .flag(
            Flag::new()
                .name("version")
                .short_code("v")
                .action(Action::StoreTrue)
                .value_type(ValueType::Bool),
        )
        .flag(
            Flag::new()
                .name("in-file")
                .short_code("i")
                .help_string("an input source file.")
                .value_type(ValueType::Str),
        )
        .flag(
            Flag::new()
                .name("out-file")
                .short_code("o")
                .help_string("an output path assembly")
                .value_type(ValueType::Str)
                .default_value(Value::Str("a.s".to_string())),
        )
        .handler(Box::new(|c| {
            let inf = c.get("in-file");
            let ouf = c.get("out-file");
            match (inf, ouf) {
                (Some(Value::Str(in_f)), Some(Value::Str(out_f))) => Ok((in_f, out_f)),
                _ => Err(RuntimeError::InvalidArguments(ROOT_HELP_STRING.to_string())),
            }
            .map(|(in_f, out_f)| {
                read_src_file(&in_f)
                    .map(|input| compile(&input))?
                    .map(|asm| write_dest_file(&out_f, &asm.as_bytes()).map(|_| EXIT_SUCCESS))?
            })
            .and_then(std::convert::identity)
            .map_err(|e| format!("{}", e))
        }))
        .run(args)
        .unwrap()
        .dispatch();

    match res {
        Ok(_) => (),
        Err(e) => {
            println!("{}", e);
            std::process::exit(1)
        }
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
        .map(|ast_node| x86_64::X86_64.generate(&mut symbol_table, ast_node.to_owned()))
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
        .map(|insts: Vec<String>| {
            let contents = insts.into_iter().collect::<String>();
            contents
        })
        .map_err(|e| RuntimeError::Undefined(format!("{:?}", e)))
}
