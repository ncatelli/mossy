use crate::stage::codegen::machine::arch::TargetArchitecture;
use crate::stage::codegen::{self, CodeGenerationErr};

use crate::stage::type_check::ast::{self, ByteSized, Type, Typed};
use crate::stage::CompilationStage;
use core::sync::atomic::{AtomicUsize, Ordering};

static BLOCK_ID: AtomicUsize = AtomicUsize::new(0);

use super::allocator::{
    self,
    register::{
        BasePointerRegister, GPRegisterAllocator, GeneralPurposeRegister, IntegerRegister,
        OperandWidth, PointerRegister, WidthFormatted,
    },
    RegisterOrOffset, SysVAllocator,
};

/// Operand represents a type that can be used as a return value register.
/// Typically this will be either a register or memory offset.
trait Operand: WidthFormatted + Copy {}

impl Operand for GeneralPurposeRegister {}
impl Operand for &GeneralPurposeRegister {}
impl Operand for allocator::register::FunctionPassingRegisters {}
impl Operand for &allocator::register::FunctionPassingRegisters {}

impl Operand for IntegerRegister {}

impl<REG> Operand for allocator::RegisterOrOffset<REG>
where
    REG: WidthFormatted,
    Self: WidthFormatted + Copy,
{
}

impl<REG> Operand for &allocator::RegisterOrOffset<REG>
where
    REG: WidthFormatted,
    Self: WidthFormatted + Copy,
{
}

/// X86_64 represents the x86_64 bit machine target.
pub struct X86_64;

impl TargetArchitecture for X86_64 {}

impl CompilationStage<ast::TypedProgram, Vec<String>, String> for X86_64 {
    fn apply(&mut self, input: ast::TypedProgram) -> Result<Vec<String>, String> {
        input
            .defs
            .into_iter()
            .map(|global_decl| {
                let res: Result<Vec<String>, CodeGenerationErr> = match global_decl {
                    ast::TypedGlobalDecls::Func(func) => self.apply(func),
                    ast::TypedGlobalDecls::Var(ast::Declaration::Scalar(ty, identifiers)) => {
                        let globals = identifiers.iter().map(|id| vec![]).flatten().collect();
                        Ok(globals)
                    }
                    ast::TypedGlobalDecls::Var(ast::Declaration::Array { ty, id, size }) => {
                        Ok(vec![])
                    }
                    // Prototypes are dropped at the typecheck and are effectively no-ops.
                    ast::TypedGlobalDecls::FuncProto => Ok(vec![]),
                };

                res
            })
            .collect::<Result<Vec<Vec<String>>, CodeGenerationErr>>()
            .map(|insts| insts.into_iter().flatten().collect())
            .map_err(|e| format!("{:?}", e))
    }
}

impl CompilationStage<ast::TypedFunctionDeclaration, Vec<String>, CodeGenerationErr> for X86_64 {
    fn apply(
        &mut self,
        input: ast::TypedFunctionDeclaration,
    ) -> Result<Vec<String>, CodeGenerationErr> {
        let mut allocator = SysVAllocator::new(GPRegisterAllocator::default());
        allocator.allocate_new_local_stack_scope(|allocator| {
            let (id, block) = (input.id, input.block);
            let parameters = input.parameters;

            for (slot, param) in parameters.iter().enumerate() {
                allocator.calculate_and_insert_parameter_offset(slot, param);
            }

            codegen_statements(allocator, block)
                .map(|block| {
                    let last = allocator.top_of_local_stack();

                    let alignment = allocator.align_stack_pointer(last);
                    vec![]
                })
                .map(|output: Vec<Vec<String>>| {
                    output.into_iter().flatten().collect::<Vec<String>>()
                })
        })
    }
}

// used for testing.
impl CompilationStage<ast::TypedCompoundStmts, Vec<String>, CodeGenerationErr> for X86_64 {
    fn apply(&mut self, input: ast::TypedCompoundStmts) -> Result<Vec<String>, CodeGenerationErr> {
        let mut allocator = SysVAllocator::new(GPRegisterAllocator::default());
        codegen_statements(&mut allocator, input)
    }
}

fn codegen_statements(
    allocator: &mut SysVAllocator,
    input: ast::TypedCompoundStmts,
) -> Result<Vec<String>, CodeGenerationErr> {
    let stmts = Vec::<ast::TypedStmtNode>::from(input);

    stmts
        .into_iter()
        .map(|stmt| codegen_statement(allocator, stmt).map(|output| output.join("")))
        .collect::<Result<Vec<String>, _>>()
}

macro_rules! flattenable_instructions {
    ($($instruction:expr,)*) => {
        vec![
            $(
                $instruction,
            )*
        ]
        .into_iter()
        .flatten()
        .collect()
    };
}

fn codegen_statement(
    allocator: &mut SysVAllocator,
    input: ast::TypedStmtNode,
) -> Result<Vec<String>, codegen::CodeGenerationErr> {
    match input {
        ast::TypedStmtNode::Expression(expr) => {
            allocator.allocate_general_purpose_register_then(|allocator, ret| Ok(vec![]))
        }
        ast::TypedStmtNode::LocalDeclaration(dec, slot_ids) => {
            match dec {
                ast::Declaration::Scalar(ty, _) => {
                    for slot in slot_ids {
                        allocator.calculate_and_insert_local_offset(slot, ty.clone());
                    }
                }
                ast::Declaration::Array { ty, size, .. } => {
                    let slot = slot_ids.last().ok_or_else(|| {
                        codegen::CodeGenerationErr::UndefinedReference(
                            "no array slot ids for local array declaration".to_string(),
                        )
                    })?;
                    allocator.calculate_and_insert_local_offset_with_cnt(*slot, ty, size);
                }
            };

            Ok(vec![])
        }
        // with else case
        ast::TypedStmtNode::If(cond, true_case, Some(false_case)) => Ok(vec![]),
        // without else case
        ast::TypedStmtNode::If(cond, true_case, None) => Ok(vec![]),
        ast::TypedStmtNode::While(cond, block) => Ok(vec![]),
        ast::TypedStmtNode::For(preop, cond, postop, block) => Ok(vec![]),
        ast::TypedStmtNode::Return(_, _, _) => Ok(vec![]),
    }
    .map(|insts: Vec<Vec<String>>| insts.into_iter().flatten().collect())
}

fn codegen_global_str(identifier: &str, str_literal: &[u8]) -> Vec<String> {
    flattenable_instructions!(
        vec!["\t.section .rodata\n".to_string()],
        codegen_label(identifier),
        str_literal
            .iter()
            .map(|c| format!("\t.byte\t{}\n", c))
            .collect::<Vec<String>>(),
        vec!["\t.byte\t0\n".to_string(), "\t.text\n".to_string()],
    )
}

/// Defines marker traits for objects that can be used to generate labels.
trait LabelFormattable: core::fmt::Display {}

impl LabelFormattable for &str {}
impl LabelFormattable for String {}

trait PrefixedLabel {
    fn fmt_with_prefix(&self) -> String;
}

struct LLabelPrefix<T: core::fmt::Display>(T);

impl<T> PrefixedLabel for LLabelPrefix<T>
where
    T: core::fmt::Display,
{
    fn fmt_with_prefix(&self) -> String {
        format!("L{}", self.0)
    }
}

impl<T> core::fmt::Display for LLabelPrefix<T>
where
    T: core::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.fmt_with_prefix())
    }
}

impl<T: core::fmt::Display> LabelFormattable for LLabelPrefix<T> {}

fn codegen_label<L>(block_id: L) -> Vec<String>
where
    L: LabelFormattable,
{
    vec![format!("{}:\n", block_id)]
}

fn codegen_jump<L>(block_id: L) -> Vec<String>
where
    L: LabelFormattable,
{
    vec![format!("\tjmp\t{}\n", block_id)]
}

const fn operator_suffix(width: OperandWidth) -> &'static str {
    match width {
        OperandWidth::QuadWord => "q",
        OperandWidth::DoubleWord => "l",
        OperandWidth::Word => "w",
        OperandWidth::Byte => "b",
    }
}

fn operand_width_of_type(ty: ast::Type) -> OperandWidth {
    match ty {
        Type::Integer(_, iw) => match iw {
            ast::IntegerWidth::One | ast::IntegerWidth::Eight => OperandWidth::Byte,
            ast::IntegerWidth::Sixteen => OperandWidth::Word,
            ast::IntegerWidth::ThirtyTwo => OperandWidth::DoubleWord,
            ast::IntegerWidth::SixtyFour => OperandWidth::QuadWord,
        },
        Type::Void | Type::Func(_, _) | Type::Pointer(_) => OperandWidth::QuadWord,
    }
}
