use crate::ast;
use cranelift::prelude::*;
use cranelift_codegen::isa;
use cranelift_module::{DataContext, Linkage, Module};
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
    fn compile(self, input: Vec<ast::ExprNode>) -> Result<Vec<u8>, CompileErr>;
}

pub struct Compiler {
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    data_ctx: DataContext,
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
            data_ctx: DataContext::new(),
            module,
        }
    }
}

impl Compile for Compiler {
    /// Compile a string in the toy language into machine code.
    fn compile(mut self, input: Vec<ast::ExprNode>) -> Result<Vec<u8>, CompileErr> {
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
    fn translate(&mut self, stmts: Vec<ast::ExprNode>) -> Result<(), String> {
        let int = self.module.target_config().pointer_type();

        // Our toy language currently only supports one return value, though
        // Cranelift is designed to support more.
        self.ctx.func.signature.returns.push(AbiParam::new(int));

        // Create the builder to build a function.
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        // Since this is the entry block, add block parameters corresponding to
        // the function's parameters.
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);

        // And, tell the builder that this block will have no further
        // predecessors. Since it's the entry block, it won't have any
        // predecessors.
        builder.seal_block(entry_block);

        // Now translate the statements of the function body.
        let mut trans = FunctionTranslator {
            int,
            builder,
            module: &mut self.module,
        };
        for expr in stmts {
            trans.translate_expr(expr);
        }

        // Tell the builder we're done with this function.
        trans.builder.finalize();
        Ok(())
    }
}

/// A collection of state used for translating from toy-language AST nodes
/// into Cranelift IR.
struct FunctionTranslator<'a> {
    int: types::Type,
    builder: FunctionBuilder<'a>,
    module: &'a mut ObjectModule,
}

impl<'a> FunctionTranslator<'a> {
    /// When you write out instructions in Cranelift, you get back `Value`s. You
    /// can then use these references in other instructions.
    fn translate_expr(&mut self, expr: ast::ExprNode) -> Value {
        use ast::{ExprNode, Primary};

        match expr {
            ExprNode::Primary(Primary::IntegerConstant(ast::IntegerConstant(ic))) => {
                use std::convert::TryFrom;
                let v: i64 = i64::try_from(ic).unwrap();
                self.builder.ins().iconst(self.int, v)
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
