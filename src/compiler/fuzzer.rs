use num_bigint::ToBigInt;

use rand::distributions::Standard;
use rand::prelude::Distribution;
use rand::Rng;
use rand::random;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::compiler::runtypes::RunFailure;
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

fn select_call(num: u8, prog: &FuzzProgram) -> (String, FuzzFunction) {
    let selected_num = num % prog.functions.len() as u8;
    let selected = &prog.functions[selected_num as usize];
    (format!("fun_{}", selected_num), selected.clone())
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

fn random_args(loc: Srcloc, a: ArgListType) -> SExp {
    match a {
        ArgListType::ProperList(0) => SExp::Nil(loc.clone()),
        ArgListType::ProperList(n) => {
            let random_64: u64 = random();
            let rest_result =
                random_args(loc.clone(), ArgListType::ProperList(n-1));
            SExp::Cons(
                loc.clone(),
                Rc::new(SExp::Integer(loc.clone(), random_64.to_bigint().unwrap())),
                Rc::new(rest_result)
            )
        },
        ArgListType::Structure(SExp::Nil(l)) => SExp::Nil(l.clone()),
        ArgListType::Structure(SExp::Cons(l,a,b)) => {
            let borrowed_a: &SExp = a.borrow();
            let borrowed_b: &SExp = b.borrow();
            SExp::Cons(
                loc.clone(),
                Rc::new(random_args(loc.clone(), ArgListType::Structure(borrowed_a.clone()))),
                Rc::new(random_args(loc.clone(), ArgListType::Structure(borrowed_b.clone())))
            )
        },
        ArgListType::Structure(_) => {
            let random_64: u64 = random();
            SExp::Integer(loc.clone(), random_64.to_bigint().unwrap())
        }
    }
}

impl FuzzOperation {
    pub fn to_sexp(&self, fun: &FuzzProgram, bindings: &Vec<Vec<FuzzOperation>>) -> SExp {
        let loc = Srcloc::start(&"*rng*".to_string());
        match self {
            FuzzOperation::Argref(n) => {
                let argument_num = random_u8();
                let argument = select_argument(
                    argument_num, fun, bindings
                );
                SExp::atom_from_string(loc.clone(), &argument.0)
            },
            FuzzOperation::Quote(s) => {
                SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::atom_from_string(loc.clone(), &"q".to_string())),
                    Rc::new(s.clone())
                )
            },
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
                        format!("binding_{}", i);
                    let b = &our_bindings[i];

                    bindings_done =
                        SExp::Cons(
                            loc.clone(),
                            Rc::new(SExp::Cons(
                                loc.clone(),
                                Rc::new(SExp::atom_from_string(loc.clone(), &binding_name)),
                                Rc::new(SExp::Cons(
                                    loc.clone(),
                                    Rc::new(b.to_sexp(fun, bindings)),
                                    Rc::new(SExp::Nil(loc.clone()))
                                ))
                            )),
                            Rc::new(bindings_done)
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
                        called_fun.1.args.clone(),
                        fun,
                        bindings,
                        args,
                        0
                    );
                SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::atom_from_string(loc.clone(), &called_fun.0)),
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

const MAX_DEPTH : u8 = 2;

fn make_random_call<R: Rng + ?Sized>(rng: &mut R, depth: u8) -> FuzzOperation {
    let mut args: Vec<FuzzOperation> = Vec::new();
    for i in 0..255 {
        args.push(random_operation(rng, depth + 1, false))
    }
    FuzzOperation::Call(random(), args)
}

// FuzzOperation is potentially infinite so we'll limit the depth to something
// sensible.
fn random_operation<R: Rng + ?Sized>(rng: &mut R, depth: u8, must_call: bool) -> FuzzOperation {
    if (depth >= MAX_DEPTH) {
        return FuzzOperation::Argref(random_u8());
    }

    if (must_call) {
        return make_random_call(rng, depth);
    }

    let selection = random_u8();

    if (selection < 5) {
        FuzzOperation::If(
            Rc::new(random_operation(rng, depth + 1, false)),
            Rc::new(random_operation(rng, depth + 1, false)),
            Rc::new(random_operation(rng, depth + 1, false))
        )
    } else if (selection < 10) {
        FuzzOperation::Multiply(
            Rc::new(random_operation(rng, depth + 1, false)),
            Rc::new(random_operation(rng, depth + 1, false))
        )
    } else if (selection < 20) {
        FuzzOperation::Sub(
            Rc::new(random_operation(rng, depth + 1, false)),
            Rc::new(random_operation(rng, depth + 1, false))
        )
    } else if (selection < 30) {
        FuzzOperation::Sha256(random_vector_of::<FuzzOperation>(false))
    } else if (selection < 35) {
        FuzzOperation::Let(
            random_vector_of::<FuzzOperation>(true),
            Rc::new(random_operation(rng, depth + 1, false))
        )
    } else if (selection < 50) {
        make_random_call(rng, depth + 1)
    } else if (selection < 60) {
        FuzzOperation::Quote(SExp::random_atom())
    } else {
        FuzzOperation::Argref(random_u8())
    }
}

impl Distribution<FuzzOperation> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzOperation {
        random_operation(rng, 0, false)
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
            body: random_operation(rng, 0, true)
        }
    }
}

fn loc_of(r: &Result<SExp, RunFailure>) -> Srcloc {
    r.as_ref().map(|x| x.loc()).unwrap_or_else(|e| {
        match e {
            RunFailure::RunErr(l,_) => l.clone(),
            RunFailure::RunExn(l,_) => l.clone()
        }
    })
}

fn make_assignments(program_args: Rc<SExp>, input_args: Result<SExp, RunFailure>, result_map: &mut HashMap<Vec<u8>, Result<FuzzOperation, RunFailure>>) {
    match (program_args.borrow(), input_args.borrow()) {
        (SExp::Cons(_,ph,pt), Ok(SExp::Cons(_,ih,it))) => {
            let ih_borrow: &SExp = ih.borrow();
            let it_borrow: &SExp = it.borrow();
            make_assignments(ph.clone(), Ok(ih_borrow.clone()), result_map);
            make_assignments(pt.clone(), Ok(it_borrow.clone()), result_map);
        },
        (SExp::Cons(_,ph,pt), v) => {
            make_assignments(ph.clone(), Err(RunFailure::RunErr(loc_of(v), format!("path subdividing {:?} for args {}", v, program_args.to_string()))), result_map);
            make_assignments(pt.clone(), Err(RunFailure::RunErr(loc_of(v), format!("path subdividing {:?} for args {}", v, program_args.to_string()))), result_map);
        },
        (SExp::Atom(_,name), v) => {
            result_map.insert(name.clone(), v.as_ref().map(|s| FuzzOperation::Quote(s.clone())).map_err(|e| e.clone()));
        },
        _ => { }
    }
}

fn replace_args(prog: &FuzzProgram, args: &HashMap<Vec<u8>, Result<FuzzOperation, RunFailure>>, bindings: &Vec<Vec<FuzzOperation>>) -> Result<FuzzOperation, RunFailure> {
    let loc = Srcloc::start(&"*replace_args*".to_string());
    match &prog.body {
        FuzzOperation::Argref(n) => {
            let argres = select_argument(*n, prog, bindings);
            let name_u8 = argres.0.as_bytes().to_vec();
            match args.get(&name_u8) {
                Some(v) => v.clone(),
                None => Ok(prog.body.clone())
            }
        },
        FuzzOperation::If(cond,iftrue,iffalse) => {
            let cond_borrowed: &FuzzOperation = cond.borrow();
            let iftrue_borrowed: &FuzzOperation = iftrue.borrow();
            let iffalse_borrowed: &FuzzOperation = iffalse.borrow();
            let cond_prog = prog.with_exp(cond_borrowed);
            let new_cond = replace_args(&cond_prog, args, bindings)?;
            let iftrue_prog = prog.with_exp(iftrue_borrowed);
            let new_iftrue = replace_args(&iftrue_prog, args, bindings)?;
            let iffalse_prog = prog.with_exp(iffalse_borrowed);
            let new_iffalse = replace_args(&iffalse_prog, args, bindings)?;
            Ok(FuzzOperation::If(Rc::new(new_cond), Rc::new(new_iftrue), Rc::new(new_iffalse)))
        },
        FuzzOperation::Multiply(a,b) => {
            let a_borrowed: &FuzzOperation = a.borrow();
            let b_borrowed: &FuzzOperation = b.borrow();
            let a_prog = prog.with_exp(a_borrowed);
            let b_prog = prog.with_exp(b_borrowed);
            let new_a = replace_args(&a_prog, args, bindings)?;
            let new_b = replace_args(&b_prog, args, bindings)?;
            Ok(FuzzOperation::Multiply(Rc::new(new_a), Rc::new(new_b)))
        },
        FuzzOperation::Sub(a,b) => {
            let a_borrowed: &FuzzOperation = a.borrow();
            let b_borrowed: &FuzzOperation = b.borrow();
            let a_prog = prog.with_exp(a_borrowed);
            let b_prog = prog.with_exp(b_borrowed);
            let new_a = replace_args(&a_prog, args, bindings)?;
            let new_b = replace_args(&b_prog, args, bindings)?;
            Ok(FuzzOperation::Sub(Rc::new(new_a), Rc::new(new_b)))
        },
        FuzzOperation::Sha256(inputs) => {
            let mut new_inputs = Vec::new();
            for i in inputs.iter() {
                let prog_with_i = prog.with_exp(i);
                new_inputs.push(replace_args(&prog_with_i, args, bindings)?);
            }
            Ok(FuzzOperation::Sha256(new_inputs))
        },
        FuzzOperation::Let(local_bindings,expr) => {
            let mut new_local_bindings = Vec::new();
            for b in local_bindings.iter() {
                let prog_with_b = prog.with_exp(b);
                new_local_bindings.push(replace_args(&prog_with_b, args, bindings)?);
            }
            let mut new_bindings = bindings.clone();
            new_bindings.push(new_local_bindings);
            let borrowed_expr: &FuzzOperation = expr.borrow();
            let prog_with_expr = prog.with_exp(borrowed_expr);
            let mut applied_bindings = bindings.clone();
            for b in new_bindings.iter() {
                applied_bindings.push(b.clone());
            }
            replace_args(&prog_with_expr, args, &applied_bindings)
        },
        FuzzOperation::Call(n,inputs) => {
            let mut new_inputs = Vec::new();
            for i in inputs.iter() {
                let prog_with_i = prog.with_exp(i);
                new_inputs.push(replace_args(&prog_with_i, args, bindings)?);
            }
            Ok(FuzzOperation::Call(*n,new_inputs))
        },
        FuzzOperation::Quote(sexp) => Ok(prog.body.clone())
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

    pub fn with_exp(&self, exp: &FuzzOperation) -> FuzzProgram {
        FuzzProgram {
            args: self.args.clone(),
            functions: self.functions.clone(),
            body: exp.clone()
        }
    }

    pub fn random_args(&self) -> SExp {
        let srcloc = Srcloc::start(&"*args*".to_string());
        random_args(srcloc, self.args.clone())
    }

    pub fn interpret(&self, args: SExp) -> Result<SExp, RunFailure> {
        let srcloc = Srcloc::start(&"*interp*".to_string());
        let mut assignment_map = HashMap::new();
        let prog_args_sexp = self.args.to_sexp();
        make_assignments(Rc::new(prog_args_sexp), Ok(args), &mut assignment_map);
        let translated_expr = replace_args(self, &assignment_map, &Vec::new())?;
        println!("translated_expr: {}", translated_expr.to_sexp(self, &Vec::new()).to_string());
        Ok(SExp::Nil(srcloc))
    }
}
