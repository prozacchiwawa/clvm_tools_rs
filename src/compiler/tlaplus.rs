use std::collections::{HashMap, HashSet, BTreeMap};
use std::fs;
use std::rc::Rc;

use handlebars::Handlebars;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::comptypes::{CompilerOpts, HelperForm, BodyForm};
use crate::compiler::sexp::SExp;
use crate::util::Number;

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

pub fn generate(
    opts: Rc<dyn CompilerOpts>,
    runner: Rc<dyn TRunProgram>,
    name: String,
    programs: &HashMap<String, Rc<BodyForm>>
) -> String {
    // create the handlebars registry
    let mut handlebars = Handlebars::new();

    let primary_module = fs::read_to_string("support/ChiaModel.tla")
        .expect("Something went wrong reading the file");

    handlebars.register_template_string("chiamodel", primary_module)
        .expect("chiamodel should be valid handlebars");

    let mut data = BTreeMap::new();

    // Insert replacements
    data.insert("name".to_string(), name.clone());

    let model = handlebars.render("chiamodel", &data)
        .expect("should be able to render model");

    model
}
