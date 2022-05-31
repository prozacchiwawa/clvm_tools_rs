use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::comptypes::{CompilerOpts, HelperForm};
use crate::compiler::sexp::SExp;
use crate::util::Number;

pub struct TlaPlusGenerator {
    opts: Rc<dyn CompilerOpts>,
    runner: Rc<dyn TRunProgram>,
    prims: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    helpers: Vec<HelperForm>
}

pub struct TlaPlusCase {
    name: String,
    val: TlaPlusExpression,
    perform: TlaPlusExpression
}

impl TlaPlusCase {
    pub fn to_string(&self) -> String {
        format!("{} = {} -> {}", self.name, self.val.to_string(), self.perform.to_string())
    }
}

pub enum TlaPlusUnopKind {
    Not
}

pub enum TlaPlusBinopKind {
    Eq,
    Ne,
    Gt,
    Lt,
    Ge,
    Le,
    And,
    Or,
    Plus,
    Minus,
    Times,
    Sub,
    Div,
    Mod,
}

pub enum TlaPlusExpression {
    Variable(String),
    Constant(Number),
    Pair(Rc<TlaPlusExpression>, Rc<TlaPlusExpression>),
    If(Rc<TlaPlusExpression>,Rc<TlaPlusExpression>,Rc<TlaPlusExpression>),
    Case(Vec<TlaPlusCase>),
    Call(String,Vec<TlaPlusExpression>),
    Unop(TlaPlusUnopKind, Rc<TlaPlusExpression>),
    Binop(TlaPlusBinopKind, Rc<TlaPlusExpression>, Rc<TlaPlusExpression>),
    Let(String, Rc<TlaPlusExpression>, Rc<TlaPlusExpression>),
    Choose(String, Rc<TlaPlusExpression>),
}

impl TlaPlusExpression {
    pub fn to_string(&self) -> String {
        panic!("not implemented");
    }
}

pub struct TlaPlusFunction {
    name: String,
    args: HashSet<String, TlaPlusExpression>,
    body: TlaPlusExpression
}

pub struct TlaPlusModule {
    extends: HashSet<String>,
    variables: HashSet<String>,
    functions: Vec<TlaPlusFunction>,
    toprules: HashMap<String, TlaPlusExpression>
}

impl TlaPlusGenerator {
    pub fn new(
        opts: Rc<dyn CompilerOpts>,
        runner: Rc<dyn TRunProgram>,
        prims: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
        helpers: Vec<HelperForm>
    ) -> TlaPlusGenerator {
        TlaPlusGenerator {
            opts,
            runner,
            prims,
            helpers
        }
    }

    pub fn generate(&self) -> TlaPlusModule {
        panic!("TODO");
        /*
        TlaPlusModule {
            extends: HashSet::new(),
            variables: HashSet::new(),
            functions: Vec::new(),
            toprules: HashMap::new()
        }
        */
    }
}
