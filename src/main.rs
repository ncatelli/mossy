use scrap::prelude::v1::*;
use std::env;
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::prelude::*;
use std::process;

type RuntimeResult<T> = Result<T, RuntimeError>;

const ASSEMBLER_ENV_VAR: &str = "AS";
const DEFAULT_ASSEMBLER: &str = "/usr/bin/as";
const ASSEMBLER_FLAGS: &str = "";
const LINKER_ENV_VAR: &str = "CC";
const DEFAULT_LINKER: &str = "/usr/bin/cc";
const LINKER_FLAGS: &str = "-O0 -o a";

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
    use mossy::parser;
    use mossy::preprocessor;
    use mossy::stage::codegen::machine::arch::x86_64;
    use mossy::stage::{type_check, CompilationStage};

    let input: Vec<(usize, char)> = source.chars().enumerate().collect();
    let pre_processed_input = preprocessor::pre_process(&input)
        .map_err(|e| RuntimeError::Undefined(format!("{:?}", e)))?;

    parser::parse(&pre_processed_input)
        .map(|program| {
            type_check::TypeAnalysis::default()
                .and_then(|| x86_64::X86_64)
                .apply(program)
        })
        .map_err(|e| RuntimeError::Undefined(format!("{:?}", e)))?
        .map(|insts| insts.into_iter().collect::<String>())
        .map_err(RuntimeError::Undefined)
}

fn assemble<'a, S>(filename: S) -> RuntimeResult<&'a str>
where
    S: AsRef<std::ffi::OsStr>,
{
    process::Command::new(
        env::var(ASSEMBLER_ENV_VAR).unwrap_or_else(|_| DEFAULT_ASSEMBLER.to_string()),
    )
    .args(ASSEMBLER_FLAGS.split_whitespace())
    .arg(filename)
    .output()
    .map(|_| "a.out")
    .map_err(|e| RuntimeError::Undefined(e.to_string()))
}

fn link<'a, S>(filenames: &[S]) -> RuntimeResult<&'a str>
where
    S: AsRef<std::ffi::OsStr>,
{
    process::Command::new(env::var(LINKER_ENV_VAR).unwrap_or_else(|_| DEFAULT_LINKER.to_string()))
        .args(LINKER_FLAGS.split_whitespace())
        // output binary
        .args(filenames)
        .output()
        .map(|_| "a")
        .map_err(|e| RuntimeError::Undefined(e.to_string()))
}

fn main() -> RuntimeResult<()> {
    let raw_args: Vec<String> = env::args().into_iter().collect::<Vec<String>>();
    let args = raw_args.iter().map(|a| a.as_str()).collect::<Vec<&str>>();

    // Flag Definitions
    let help = scrap::Flag::store_true("help", "h", "display usage information.").optional();
    let in_file = scrap::Flag::expect_string("in-file", "i", "an input path for a source file.");
    let out_file = scrap::Flag::expect_string("out-file", "o", "an assembly output path.")
        .optional()
        .with_default("a.s".to_string());
    let backend = scrap::Flag::with_choices(
        "backend",
        "b",
        "a target architecture backend.",
        ["x86_64".to_string()],
        scrap::StringValue,
    )
    .optional()
    .with_default("x86_64".to_string());

    let cmd = scrap::Cmd::new("mossy")
        .description("An (irresponsibly) experimental C compiler.")
        .author("Nate Catelli <ncatelli@packetfire.org>")
        .version("0.1.0")
        .with_flag(in_file)
        .with_flag(out_file)
        .with_flag(backend)
        .with_flag(help)
        .with_handler(|(((inf, ouf), _), _)| {
            read_src_file(&inf)
                .and_then(|input| compile(&input))
                .and_then(|asm| write_dest_file(&ouf, asm.as_bytes()))
                .and_then(|_| assemble(&ouf))
                .and_then(|bin_out| {
                    let bins = [bin_out, "./utils/print_int.o", "./utils/print_char.o"];
                    link(&bins)
                })
        });

    cmd.evaluate(&args[..])
        .map_err(|e| RuntimeError::Undefined(e.to_string()))
        .and_then(|(flags, help)| {
            if help.is_some() {
                println!("{}", cmd.help());
                Ok(())
            } else {
                cmd.dispatch((flags, None)).map(|_| ())
            }
        })
}
