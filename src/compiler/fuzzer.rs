use rand::distributions::Standard;
use rand::prelude::Distribution;
use rand::Rng;
use rand::random;
use std::borrow::Borrow;
use std::rc::Rc;

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

// We don't actually need all operators here, just a good selection with
// semantics that are distinguishable.
#[derive(Debug, Clone)]
pub enum FuzzOperation {
    Argref(u8),
    Quote(SExp),
    If(Rc<FuzzOperation>,Rc<FuzzOperation>,Rc<FuzzOperation>),
    Multiply(Rc<FuzzOperation>,Rc<FuzzOperation>),
    Sub(Rc<FuzzOperation>,Rc<FuzzOperation>),
    Sha256(Vec<FuzzOperation>),
    Let(Vec<FuzzOperation>,Rc<FuzzOperation>),
    Call(u8,Vec<FuzzOperation>),
}

#[derive(Debug, Clone)]
pub enum ArgListType {
    ProperList(u8),
    Structure(SExp),
}

#[derive(Debug, Clone)]
pub struct FuzzFunction {
    pub inline: bool,
    pub number: u8,
    pub args: ArgListType,
    pub body: FuzzOperation,
}

#[derive(Debug)]
pub struct FuzzProgram {
    pub args: ArgListType,
    pub functions: Vec<FuzzFunction>,
    pub body: FuzzOperation,
}

fn random_u8() -> u8 {
    random()
}

fn atom_list(sexp: &SExp) -> Vec<String> {
    match sexp {
        SExp::Nil(_) => vec!(),
        SExp::Atom(_,a) => vec!(sexp.to_string()),
        SExp::QuotedString(_,_,a) => vec!(sexp.to_string()),
        SExp::Integer(_,i) => vec!(sexp.to_string()),
        SExp::Cons(_,a,b) => {
            let mut a_vec = atom_list(a.borrow());
            let b_vec = atom_list(b.borrow());
            for b_item in b_vec.iter() {
                a_vec.push(b_item.clone());
            }
            a_vec
        }
    }
}

fn select_argument(num_: u8, fun: &FuzzProgram, bindings: &Vec<Vec<FuzzOperation>>) -> (String, FuzzOperation) {
    let mut num = num_;
    let args = atom_list(&fun.args.to_sexp());

    loop {
        if (num < args.len() as u8) {
            return (args[num as usize].clone(), FuzzOperation::Argref(num));
        }

        num -= args.len() as u8;
        let mut binding_count = 0;
        for b_list in bindings {
            if num < b_list.len() as u8 {
                return (
                    format!("binding_{}", binding_count + num),
                    b_list[num as usize].clone()
                );
            }

            num -= b_list.len() as u8;
            binding_count += b_list.len() as u8;
        }
    }
}

fn select_call(num: u8, prog: &FuzzProgram) -> String {
    format!("function_{}", (num % prog.functions.len() as u8))
}

fn make_operator(op: String, args: Vec<SExp>) -> SExp {
    let loc = Srcloc::start(&"*rng*".to_string());
    let mut result = SExp::Nil(loc.clone());

    for i_reverse in 0..args.len() {
        let i = args.len() - i_reverse - 1;
        result = SExp::Cons(
            loc.clone(),
            Rc::new(args[i].clone()),
            Rc::new(result)
        );
    }

    SExp::Cons(
        loc.clone(),
        Rc::new(SExp::atom_from_string(loc.clone(), &op)),
        Rc::new(result)
    )
}

fn distribute_args(a: ArgListType, fun: &FuzzProgram, bindings: &Vec<Vec<FuzzOperation>>, arginputs: &Vec<FuzzOperation>, argn: u8) -> (u8, SExp) {
    let loc = Srcloc::start(&"*rng*".to_string());
    match a {
        ArgListType::ProperList(0) => (argn, SExp::Nil(loc.clone())),
        ArgListType::ProperList(n) => {
            let rest_result =
                distribute_args(
                    ArgListType::ProperList(n-1),
                    fun,
                    bindings,
                    arginputs,
                    argn + 1
                );
            (
                rest_result.0,
                SExp::Cons(
                    loc.clone(),
                    Rc::new(arginputs[argn as usize].to_sexp(
                        fun,
                        bindings
                    )),
                    Rc::new(rest_result.1)
                )
            )
        },
        ArgListType::Structure(SExp::Nil(l)) => (argn, SExp::Nil(l.clone())),
        ArgListType::Structure(SExp::Cons(l,a,b)) => {
            let a_borrow: &SExp = a.borrow();
            let b_borrow: &SExp = b.borrow();
            let first_res =
                distribute_args(
                    ArgListType::Structure(a_borrow.clone()),
                    fun,
                    bindings,
                    arginputs,
                    argn
                );
            let rest_res =
                distribute_args(
                    ArgListType::Structure(b_borrow.clone()),
                    fun,
                    bindings,
                    arginputs,
                    argn + first_res.0
                );
            (
                rest_res.0,
                make_operator(
                    "c".to_string(), vec!(first_res.1, rest_res.1)
                )
            )
        },
        ArgListType::Structure(_) => {
            (
                argn + 1_u8,
                arginputs[argn as usize].to_sexp(
                    fun,
                    bindings
                )
            )
        }
    }
}

impl FuzzOperation {
    fn to_sexp(&self, fun: &FuzzProgram, bindings: &Vec<Vec<FuzzOperation>>) -> SExp {
        let loc = Srcloc::start(&"*rng*".to_string());
        match self {
            FuzzOperation::Argref(n) => {
                let argument_num = random_u8();
                let argument = select_argument(
                    argument_num, fun, bindings
                );
                SExp::atom_from_string(loc.clone(), &argument.0)
            },
            FuzzOperation::Quote(s) => make_operator("q".to_string(), vec!(s.clone())),
            FuzzOperation::If(cond,ct,cf) => make_operator(
                "if".to_string(),
                vec!(
                    cond.to_sexp(fun, bindings),
                    ct.to_sexp(fun, bindings),
                    cf.to_sexp(fun, bindings)
                )
            ),
            FuzzOperation::Multiply(a,b) => make_operator(
                "*".to_string(),
                vec!(
                    a.to_sexp(fun, bindings),
                    b.to_sexp(fun, bindings)
                )
            ),
            FuzzOperation::Sub(a,b) => make_operator(
                "-".to_string(),
                vec!(
                    a.to_sexp(fun, bindings),
                    b.to_sexp(fun, bindings)
                )
            ),
            FuzzOperation::Sha256(ents) => make_operator(
                "sha256".to_string(),
                ents.iter().map(|x| x.to_sexp(fun, bindings)).collect()
            ),
            FuzzOperation::Let(our_bindings,body) => {
                let loc = Srcloc::start(&"*rng*".to_string());
                let mut bindings_done = SExp::Nil(loc.clone());

                for i_reverse in 0..our_bindings.len() {
                    let i = our_bindings.len() - i_reverse - 1;
                    let binding_name =
                        format!("binding_{}", i_reverse);
                    let b = &our_bindings[i];

                    bindings_done =
                        SExp::Cons(
                            loc.clone(),
                            Rc::new(SExp::atom_from_string(loc.clone(), &binding_name)),
                            Rc::new(b.to_sexp(fun, bindings))
                        );
                }

                let mut inner_bindings = bindings.clone();
                inner_bindings.push(our_bindings.clone());

                make_operator(
                    "let".to_string(),
                    vec!(
                        bindings_done,
                        body.to_sexp(
                            fun,
                            &inner_bindings
                        )
                    )
                )
            },
            FuzzOperation::Call(selection,args) => {
                let loc = Srcloc::start(&"*rng*".to_string());
                let called_fun = select_call(random_u8(), fun);
                let args =
                    distribute_args(
                        fun.args.clone(),
                        fun,
                        bindings,
                        args,
                        0
                    );
                SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::atom_from_string(loc.clone(), &called_fun)),
                    Rc::new(args.1)
                )
            }
        }
    }
}

fn random_vector_of<T>(at_least_one: bool) -> Vec<T> where Standard: Distribution<T> {
    let mut args: Vec<T> = Vec::new();

    if at_least_one {
        args.push(random());
    }

    loop {
        let rnd = random_u8();
        if rnd < 192 {
            args.push(random());
        } else {
            break;
        }
    }

    return args;
}

impl Distribution<FuzzOperation> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzOperation {
        match rng.gen_range(0..=7) {
            0 => FuzzOperation::Argref(random()),
            1 => FuzzOperation::Quote(random()),
            2 => {
                FuzzOperation::If(
                    Rc::new(random()),
                    Rc::new(random()),
                    Rc::new(random())
                )
            },
            3 => FuzzOperation::Multiply(Rc::new(random()), Rc::new(random())),
            4 => FuzzOperation::Sub(Rc::new(random()), Rc::new(random())),
            5 => FuzzOperation::Sha256(random_vector_of::<FuzzOperation>(true)),
            6 => {
                FuzzOperation::Let(
                    random_vector_of::<FuzzOperation>(true),
                    Rc::new(random())
                )
            },
            _ => {
                let mut args: Vec<FuzzOperation> = Vec::new();
                for i in 0..255 {
                    args.push(random())
                }
                FuzzOperation::Call(random(), args)
            }
        }
    }
}

impl Distribution<ArgListType> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> ArgListType {
        match rng.gen_range(0..=1) {
            0 => ArgListType::ProperList(rng.gen_range(0..=5)),
            _ => ArgListType::Structure(random())
        }
    }
}

impl ArgListType {
    fn random_args(&self) -> SExp {
        let loc = Srcloc::start(&"*rng*".to_string());
        match self {
            ArgListType::ProperList(n) => {
                let mut args = SExp::Nil(loc.clone());
                for i_reverse in 0..*n {
                    let i = n - i_reverse;
                    args = SExp::Cons(
                        args.loc(),
                        Rc::new(SExp::atom_from_vec(
                            loc.clone(),
                            &random_vector_of::<u8>(false)
                        )),
                        Rc::new(args.clone())
                    );
                }
                args
            },
            ArgListType::Structure(SExp::Nil(l)) => SExp::Nil(l.clone()),
            ArgListType::Structure(SExp::Cons(l,a,b)) => {
                let aborrow: &SExp = a.borrow();
                let bborrow: &SExp = b.borrow();
                let aclone = aborrow.clone();
                let bclone = bborrow.clone();
                let arg_a = ArgListType::Structure(aclone).random_args();
                let arg_b = ArgListType::Structure(bclone).random_args();
                SExp::Cons(l.clone(), Rc::new(arg_a), Rc::new(arg_b))
            },
            ArgListType::Structure(x) => random(),
        }
    }

    fn to_sexp(&self) -> SExp {
        let loc = Srcloc::start(&"*rng*".to_string());
        match self {
            ArgListType::ProperList(n) => {
                let mut args = SExp::Nil(loc.clone());
                for i_reverse in 0..*n {
                    let i = n - i_reverse;
                    args = SExp::Cons(
                        args.loc(),
                        Rc::new(SExp::atom_from_string(
                            loc.clone(), &format!("arg_{}", i)
                        )),
                        Rc::new(args.clone())
                    );
                }
                args
            },
            ArgListType::Structure(s) => { s.clone() }
        }
    }
}

impl Distribution<FuzzFunction> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzFunction {
        FuzzFunction {
            inline: random(),
            number: 0,
            args: random(),
            body: random()
        }
    }
}

impl FuzzFunction {
    fn to_sexp(&self, fun: &FuzzProgram) -> SExp {
        let fuzzloc = Srcloc::start(&"*fuzz*".to_string());
        let initial_atom =
            if (self.inline) {
                SExp::atom_from_string(
                    fuzzloc.clone(),
                    &"defun-inline".to_string()
                )
            } else {
                SExp::atom_from_string(
                    fuzzloc.clone(),
                    &"defun".to_string()
                )
            };
        let name_atom =
            SExp::atom_from_string(
                fuzzloc.clone(),
                &format!("fun_{}", self.number)
            );
        let args_sexp = self.args.to_sexp();
        let body_sexp = self.body.to_sexp(&self.to_program(fun), &Vec::new());
        SExp::Cons(
            fuzzloc.clone(),
            Rc::new(initial_atom),
            Rc::new(SExp::Cons(
                fuzzloc.clone(),
                Rc::new(name_atom),
                Rc::new(SExp::Cons(
                    fuzzloc.clone(),
                    Rc::new(args_sexp),
                    Rc::new(SExp::Cons(
                        fuzzloc.clone(),
                        Rc::new(body_sexp),
                        Rc::new(SExp::Nil(fuzzloc.clone()))
                    ))
                ))
            ))
        )
    }

    fn to_program(&self, parent: &FuzzProgram) -> FuzzProgram {
        FuzzProgram {
            args: self.args.clone(),
            functions: parent.functions.clone(),
            body: self.body.clone()
        }
    }
}

/*
 * Produce chialisp frontend code with an expected result
 */
impl Distribution<FuzzProgram> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzProgram {
        let funs = random_vector_of::<FuzzFunction>(true).iter().enumerate().map(|(i, f)| {
            let mut fcopy = f.clone();
            fcopy.number = i as u8;
            fcopy
        }).collect();
        FuzzProgram {
            args: random(),
            functions: funs,
            body: random()
        }
    }
}

impl FuzzProgram {
    pub fn to_sexp(&self) -> SExp {
        let mut body_vec = Vec::new();
        body_vec.push(self.args.to_sexp());
        for f in &self.functions {
            body_vec.push(f.to_sexp(self))
        }
        body_vec.push(self.body.to_sexp(self, &Vec::new()));
        make_operator("mod".to_string(), body_vec)
    }
}
