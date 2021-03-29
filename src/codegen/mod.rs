use crate::ast;
use cranelift::prelude::*;
use cranelift_codegen::ir::{types, AbiParam, InstBuilder};
use cranelift_codegen::isa;
use cranelift_codegen::settings;
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

use target_lexicon;

#[derive(Clone, PartialEq)]
pub enum CompileErr {
    Unspecified(String),
}

impl std::fmt::Debug for CompileErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileErr::Unspecified(e) => write!(f, "unspecified compilation err: {}", e),
        }
    }
}

pub trait Compile {
    fn compile(self, input: ast::ExprNode) -> Result<Vec<u8>, CompileErr>;
}

pub struct Compiler {
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    module: ObjectModule,
}

impl Default for Compiler {
    fn default() -> Self {
        let shared_builder = settings::builder();
        let shared_flags = settings::Flags::new(shared_builder);
        let triple = target_lexicon::DefaultToHost::default().0;
        let target_isa = isa::lookup(triple).unwrap().finish(shared_flags);
        let builder = ObjectBuilder::new(
            target_isa,
            "mossy-C",
            cranelift_module::default_libcall_names(),
        )
        .unwrap();
        let module = ObjectModule::new(builder);

        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            module,
        }
    }
}

impl Compile for Compiler {
    /// Compile a string in the toy language into machine code.
    fn compile(mut self, input: ast::ExprNode) -> Result<Vec<u8>, CompileErr> {
        // Then, translate the AST nodes into Cranelift IR.
        self.translate(input).map_err(CompileErr::Unspecified)?;

        let id = self
            .module
            .declare_function("main", Linkage::Export, &self.ctx.func.signature)
            .map_err(|e| e.to_string())
            .map_err(CompileErr::Unspecified)?;

        self.module
            .define_function(id, &mut self.ctx, &mut codegen::binemit::NullTrapSink {})
            .map_err(|e| e.to_string())
            .map_err(CompileErr::Unspecified)?;

        self.module.clear_context(&mut self.ctx);

        let op = self.module.finish();
        op.emit()
            .map_err(|e| CompileErr::Unspecified(e.to_string()))
    }
}

impl Compiler {
    fn translate(&mut self, input: ast::ExprNode) -> Result<(), String> {
        let pointer_type = self.module.target_config().pointer_type();
        self.ctx
            .func
            .signature
            .returns
            .push(AbiParam::new(pointer_type));

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
        let entry_block = builder.create_block();

        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let mut translator = FunctionTranslator {
            pointer_type,
            builder,
        };

        let ret = translator.translate_expr(input);

        // return and finalize
        translator.builder.ins().return_(&[ret]);
        translator.builder.finalize();

        Ok(())
    }
}

struct FunctionTranslator<'a> {
    pointer_type: types::Type,
    builder: FunctionBuilder<'a>,
}

impl<'a> FunctionTranslator<'a> {
    fn translate_expr(&mut self, expr: ast::ExprNode) -> Value {
        use ast::{ExprNode, Primary};

        match expr {
            ExprNode::Primary(Primary::IntegerConstant(ast::IntegerConstant(ic))) => {
                use std::convert::TryFrom;
                let v: i64 = i64::try_from(ic).unwrap();
                self.builder.ins().iconst(self.pointer_type, v)
            }

            ExprNode::Addition(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().iadd(lhs, rhs)
            }

            ExprNode::Subtraction(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().isub(lhs, rhs)
            }

            ExprNode::Multiplication(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().imul(lhs, rhs)
            }

            ExprNode::Division(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().udiv(lhs, rhs)
            }
        }
    }
}
