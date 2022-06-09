use scrap::prelude::v1::*;
use std::env;
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::process;

type RuntimeResult<T> = Result<T, RuntimeError>;

const ASSEMBLER_ENV_VAR: &str = "AS";
const DEFAULT_ASSEMBLER: &str = "/usr/bin/as";
const ASSEMBLER_FLAGS: &str = "";
const LINKER_ENV_VAR: &str = "CC";
const DEFAULT_LINKER: &str = "/usr/bin/cc";
const LINKER_FLAGS: &str = "-O0";

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

fn read_src_file<P: AsRef<Path>>(filename: P) -> RuntimeResult<String> {
    let mut f = File::open(filename).map_err(|_| RuntimeError::FileUnreadable)?;

    let mut contents = String::new();
    match f.read_to_string(&mut contents) {
        Ok(_) => Ok(contents),
        Err(e) => Err(RuntimeError::Undefined(e.to_string())),
    }
}

fn write_dest_file<P: AsRef<Path>>(filename: P, data: &[u8]) -> RuntimeResult<()> {
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
    use mossy::lexer;
    use mossy::parser;
    use mossy::preprocessor;
    use mossy::stage::codegen::machine::arch::x86_64;
    use mossy::stage::{type_check, CompilationStage};

    let input: Vec<(usize, char)> = source.chars().enumerate().collect();
    let pre_processed_input = preprocessor::pre_process(&input)
        .map_err(|e| RuntimeError::Undefined(format!("{:?}", e)))?;

    let preprocessed: String = pre_processed_input.into_iter().map(|(_, c)| c).collect();
    lexer::rewrite::lex(&preprocessed)
        .map(|t| {
            t.into_iter()
                .enumerate()
                .collect::<Vec<(usize, lexer::rewrite::Token)>>()
        })
        .and_then(|tokens| {
            parser::parse(&tokens)
                .map_err(|e| format!("{:?}", e))
                .and_then(|program| {
                    type_check::TypeAnalysis::default()
                        .and_then(|| x86_64::X86_64)
                        .apply(program)
                })
        })
        .map_err(RuntimeError::Undefined)
        .map(|insts| insts.into_iter().collect::<String>())
}

fn assemble<P>(filename: P) -> RuntimeResult<PathBuf>
where
    P: AsRef<Path>,
{
    // convert the filepath to a .out file.
    let output_filename = filename.as_ref().with_extension("out");

    process::Command::new(
        env::var(ASSEMBLER_ENV_VAR).unwrap_or_else(|_| DEFAULT_ASSEMBLER.to_string()),
    )
    .args(ASSEMBLER_FLAGS.split_whitespace())
    .args(format!("-o {}", &output_filename.display()).split_whitespace())
    .arg(filename.as_ref().as_os_str())
    .output()
    .map(|_| output_filename)
    .map_err(|e| RuntimeError::Undefined(e.to_string()))
}

fn link<I, O>(output_file: O, filenames: &[I]) -> RuntimeResult<()>
where
    I: AsRef<Path>,
    O: AsRef<Path>,
{
    process::Command::new(env::var(LINKER_ENV_VAR).unwrap_or_else(|_| DEFAULT_LINKER.to_string()))
        .args(LINKER_FLAGS.split_whitespace())
        .args(
            format!("-o {}", &output_file.as_ref().with_extension("").display()).split_whitespace(),
        )
        // output binary
        .args(filenames.iter().map(|f| f.as_ref().as_os_str()))
        .output()
        .map(|_| ())
        .map_err(|e| RuntimeError::Undefined(e.to_string()))
}

fn main() -> RuntimeResult<()> {
    let raw_args: Vec<String> = env::args().into_iter().collect::<Vec<String>>();
    let args = raw_args.iter().map(|a| a.as_str()).collect::<Vec<&str>>();

    // Flag Definitions
    let help = scrap::Flag::store_true("help", "h", "display usage information.").optional();
    let out_file = scrap::Flag::expect_string("out-file", "o", "a binary output path.").optional();
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
        .with_flag(out_file)
        .with_flag(backend)
        .with_flag(help)
        .with_args_handler(|args, ((ouf, _), _)| {
            let (src_files, obj_files) = args
                .into_iter()
                .map(|val| val.unwrap())
                .filter(|s| s.ends_with(".c") || s.ends_with(".o"))
                .fold((vec![], vec![]), |(mut src_files, mut obj_files), file| {
                    if file.ends_with(".c") {
                        src_files.push(Path::new(&file).to_path_buf())
                    } else {
                        obj_files.push(Path::new(&file).to_path_buf())
                    }
                    (src_files, obj_files)
                });

            // collect all complied and assembled object paths
            let assembled_objects: Vec<PathBuf> = src_files
                .into_iter()
                .map(|file| {
                    read_src_file(&file)
                        .and_then(|input| compile(&input))
                        .and_then(|asm| {
                            let asm_out_file = Path::new(&file).with_extension("s");
                            write_dest_file(&asm_out_file, asm.as_bytes()).map(|_| asm_out_file)
                        })
                        .and_then(|asm_src| assemble(&asm_src))
                })
                .collect::<Result<_, RuntimeError>>()?;

            // collect all object file paths
            let obj_files: Vec<PathBuf> = assembled_objects
                .into_iter()
                .chain(obj_files.into_iter().map(|f| Path::new(&f).to_path_buf()))
                .collect();

            // determine the output file name
            let output_file = ouf
                .map(|f| Path::new(&f).to_path_buf())
                .and(obj_files.first().map(|f| f.to_path_buf()))
                .ok_or(RuntimeError::FileUnreadable)?;

            // link all binaries
            link(&output_file, &obj_files)
        });

    cmd.evaluate(&args[..])
        .map_err(|e| RuntimeError::Undefined(format!("{}\n{}", e, cmd.help())))
        .and_then(
            |scrap::Value {
                 span,
                 value: (flags, help),
             }| {
                if help.is_some() {
                    println!("{}", cmd.help());
                    Ok(())
                } else {
                    let unmatched_args = scrap::return_unused_args(&args[..], &span);
                    cmd.dispatch_with_args(unmatched_args, Value::new(span, (flags, help)))
                        .map(|_| ())
                }
            },
        )
}
