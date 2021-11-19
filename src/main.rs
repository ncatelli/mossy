use scrap::prelude::v1::*;
use std::env;
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::prelude::*;

type RuntimeResult<T> = Result<T, RuntimeError>;

/// Represents an error that can return an exit code.
trait ErrorWithExitCode {
    /// Returns an exit status for a given error;
    fn exit_code(&self) -> i32;
}

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

impl ErrorWithExitCode for RuntimeError {
    fn exit_code(&self) -> i32 {
        match self {
            Self::FileUnreadable => 1,
            Self::Undefined(_) => 127,
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
    use mossy::stage::codegen::machine::arch::x86_64;
    use mossy::stage::{type_check, CompilationStage};

    let input: Vec<(usize, char)> = source.chars().enumerate().collect();

    parser::parse(&input)
        .map(|program| {
            type_check::TypeAnalysis::new()
                .and_then(|| x86_64::X86_64)
                .apply(program)
        })
        .map_err(|e| RuntimeError::Undefined(format!("{:?}", e)))?
        .map(|insts| {
            x86_64::codegen_preamble()
                .into_iter()
                .chain(insts.into_iter())
                .collect::<String>()
        })
        .map_err(|e| RuntimeError::Undefined(format!("{:?}", e)))
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
        .with_flag(
            scrap::Flag::with_choices(
                "backend",
                "b",
                "a target architecture backend.",
                ["x86_64".to_string()],
                scrap::StringValue,
            )
            .optional()
            .with_default("x86_64".to_string()),
        )
        .with_handler(|((inf, ouf), _)| {
            read_src_file(&inf)
                .and_then(|input| compile(&input))
                .and_then(|asm| write_dest_file(&ouf, asm.as_bytes()))
        });

    let help_string = cmd.help();
    let eval_res = cmd
        .evaluate(&args[..])
        .map_err(|e| RuntimeError::Undefined(e.to_string()))
        .and_then(|flags| cmd.dispatch(flags));

    match eval_res {
        Ok(_) => (),
        Err(RuntimeError::FileUnreadable) => {
            println!("unknown input file\n{}", &help_string);
            std::process::exit(1)
        }

        Err(RuntimeError::Undefined(e)) => {
            println!("{}\n{}", e, &help_string);
            std::process::exit(RuntimeError::Undefined(e).exit_code())
        }
    }
}
