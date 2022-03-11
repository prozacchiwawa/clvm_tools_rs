use num_bigint::{BigInt, ToBigInt};

use rand::distributions::Standard;
use rand::prelude::Distribution;
use rand::Rng;
use rand::random;

use sha2::{Sha256, Digest};

use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

use crate::classic::clvm::casts::{bigint_to_bytes, TConvertOption};

use crate::compiler::clvm::truthy;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{SExp, parse_sexp};
use crate::compiler::srcloc::Srcloc;

use rand::SeedableRng;
use rand::rngs::SmallRng;

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

fn fuzz_num(x: i32) -> FuzzOperation {
    let loc = Srcloc::start(&"*int*".to_string());
    FuzzOperation::Quote(SExp::Integer(loc, x.to_bigint().unwrap()))
}

fn fuzz_bignum(s: &str) -> FuzzOperation {
    let loc = Srcloc::start(&"*int*".to_string());
    FuzzOperation::Quote(SExp::Integer(loc, BigInt::parse_bytes(s.as_bytes(), 10).unwrap()))
}

fn fuzz_nil() -> FuzzOperation {
    let loc = Srcloc::start(&"*nil*".to_string());
    FuzzOperation::Quote(SExp::Nil(loc))
}

impl PartialEq for FuzzOperation {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (FuzzOperation::Argref(x), FuzzOperation::Argref(y)) => x == y,
            (FuzzOperation::Quote(a), FuzzOperation::Quote(b)) => a == b,
            (FuzzOperation::If(conda,thena,elsea), FuzzOperation::If(condb,thenb,elseb)) => {
                let avec: Vec<&FuzzOperation> =
                    vec!(conda.borrow(), thena.borrow(), elsea.borrow());
                let bvec: Vec<&FuzzOperation> =
                    vec!(condb.borrow(), thenb.borrow(), elseb.borrow());
                avec == bvec
            },
            (FuzzOperation::Multiply(ma,na), FuzzOperation::Multiply(mb,nb)) => {
                let avec: Vec<&FuzzOperation> =
                    vec!(ma.borrow(), na.borrow());
                let bvec: Vec<&FuzzOperation> =
                    vec!(mb.borrow(), nb.borrow());
                avec == bvec
            },
            (FuzzOperation::Sub(ma,na), FuzzOperation::Sub(mb,nb)) => {
                let avec: Vec<&FuzzOperation> =
                    vec!(ma.borrow(), na.borrow());
                let bvec: Vec<&FuzzOperation> =
                    vec!(mb.borrow(), nb.borrow());
                avec == bvec
            },
            (FuzzOperation::Sha256(a), FuzzOperation::Sha256(b)) => a == b,
            (FuzzOperation::Let(bindings_a, body_a), FuzzOperation::Let(bindings_b, body_b)) => {
                let a_borrow: &FuzzOperation = body_a.borrow();
                let b_borrow: &FuzzOperation = body_b.borrow();
                bindings_a == bindings_b && a_borrow == b_borrow
            },
            (FuzzOperation::Call(a,alist), FuzzOperation::Call(b,blist)) => a == b && alist == blist,
            _ => false
        }
    }
}

impl Eq for FuzzOperation { }

#[derive(Debug, Clone)]
pub enum ArgListType {
    ProperList(u8),
    Structure(SExp),
}

#[derive(Debug, Clone)]
pub enum ArgInputs {
    List(Vec<FuzzOperation>),
    Atom(FuzzOperation),
    Cons(FuzzOperation, FuzzOperation)
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

fn random_u8<R: Rng + ?Sized>(rng: &mut R) -> u8 where Standard: Distribution<u8> {
    rng.gen()
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

fn select_argument(num_: u8, fun: &FuzzProgram, bindings: &Vec<Vec<FuzzOperation>>) -> Option<(String, FuzzOperation)> {
    let mut num = num_;
    let args_sexp = fun.args.to_sexp();
    let args = atom_list(&args_sexp);

    if args.len() == 0 && bindings.len() == 0 {
        return None;
    }

    loop {
        if (num < args.len() as u8) {
            return Some((args[num as usize].clone(), FuzzOperation::Argref(num)));
        }

        num -= args.len() as u8;
        let mut binding_count = 0;
        for b_list in bindings {
            if num < b_list.len() as u8 {
                return Some((
                    format!("binding_{}", binding_count + num),
                    b_list[num as usize].clone()
                ));
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

fn distribute_args(a: &ArgListType, fun: &FuzzProgram, bindings: &Vec<Vec<FuzzOperation>>, arginputs: &Vec<FuzzOperation>, convert: &dyn Fn(FuzzOperation) -> FuzzOperation, argn: u8) -> (u8, SExp) {
    let loc = Srcloc::start(&"*rng*".to_string());
    match a {
        ArgListType::ProperList(0) => (argn, SExp::Nil(loc.clone())),
        ArgListType::ProperList(n) => {
            let rest_result =
                distribute_args(
                    &ArgListType::ProperList(n-1),
                    fun,
                    bindings,
                    arginputs,
                    convert,
                    argn + 1
                );
            let head_result = convert(arginputs[argn as usize].clone()).to_sexp(
                fun,
                bindings,
                false,
            );
            (
                rest_result.0,
                SExp::Cons(
                    loc.clone(),
                    Rc::new(head_result),
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
                    &ArgListType::Structure(a_borrow.clone()),
                    fun,
                    bindings,
                    arginputs,
                    convert,
                    argn,
                );
            let rest_res =
                distribute_args(
                    &ArgListType::Structure(b_borrow.clone()),
                    fun,
                    bindings,
                    arginputs,
                    convert,
                    first_res.0,
                );
            (
                rest_res.0,
                SExp::Cons(l.clone(), Rc::new(first_res.1), Rc::new(rest_res.1))
            )
        },
        ArgListType::Structure(_) => {
            let converted = convert(arginputs[argn as usize].clone()).to_sexp(
                fun,
                bindings,
                false
            );
            (argn + 1_u8, converted)
        }
    }
}

fn random_args<R: Rng + ?Sized>(rng: &mut R, loc: Srcloc, a: ArgListType) -> SExp {
    match a {
        ArgListType::ProperList(0) => SExp::Nil(loc.clone()),
        ArgListType::ProperList(n) => {
            let random_64: u64 = rng.gen();
            let rest_result =
                random_args(rng, loc.clone(), ArgListType::ProperList(n-1));
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
                Rc::new(random_args(rng, loc.clone(), ArgListType::Structure(borrowed_a.clone()))),
                Rc::new(random_args(rng, loc.clone(), ArgListType::Structure(borrowed_b.clone())))
            )
        },
        ArgListType::Structure(_) => {
            let random_64: u64 = rng.gen();
            SExp::Integer(loc.clone(), random_64.to_bigint().unwrap())
        }
    }
}

impl FuzzOperation {
    pub fn to_sexp(&self, fun: &FuzzProgram, bindings: &Vec<Vec<FuzzOperation>>, quotes: bool) -> SExp {
        let loc = Srcloc::start(&"*rng*".to_string());
        match self {
            FuzzOperation::Argref(n) => {
                select_argument(
                    *n, fun, bindings
                ).map(|argument| {
                    SExp::atom_from_string(loc.clone(), &argument.0)
                }).unwrap_or_else(|| SExp::Nil(loc.clone()))
            },
            FuzzOperation::Quote(s) => {
                if quotes {
                    SExp::Cons(
                        loc.clone(),
                        Rc::new(SExp::atom_from_string(loc.clone(), &"q".to_string())),
                        Rc::new(s.clone())
                    )
                } else {
                    s.clone()
                }
            },
            FuzzOperation::If(cond,ct,cf) => make_operator(
                "if".to_string(),
                vec!(
                    cond.to_sexp(fun, bindings, true),
                    ct.to_sexp(fun, bindings, true),
                    cf.to_sexp(fun, bindings, true)
                )
            ),
            FuzzOperation::Multiply(a,b) => make_operator(
                "*".to_string(),
                vec!(
                    a.to_sexp(fun, bindings, true),
                    b.to_sexp(fun, bindings, true)
                )
            ),
            FuzzOperation::Sub(a,b) => make_operator(
                "-".to_string(),
                vec!(
                    a.to_sexp(fun, bindings, true),
                    b.to_sexp(fun, bindings, true)
                )
            ),
            FuzzOperation::Sha256(ents) => make_operator(
                "sha256".to_string(),
                ents.iter().map(|x| x.to_sexp(fun, bindings, true)).collect()
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
                                    Rc::new(b.to_sexp(fun, bindings, true)),
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
                            &inner_bindings,
                            true
                        )
                    )
                )
            },
            FuzzOperation::Call(selection,args) => {
                let loc = Srcloc::start(&"*rng*".to_string());
                let called_fun = select_call(*selection, fun);
                let args =
                    distribute_args(
                        &called_fun.1.args,
                        fun,
                        bindings,
                        args,
                        &|x| x,
                        0,
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

fn random_vector_of<T, R: Rng + ?Sized>(rng: &mut R, at_least_one: bool) -> Vec<T> where Standard: Distribution<T> {
    let mut args: Vec<T> = Vec::new();

    if at_least_one {
        args.push(rng.gen());
    }

    loop {
        let rnd = random_u8(rng);
        if rnd < 192 {
            args.push(rng.gen());
        } else {
            break;
        }
    }

    return args;
}

const MAX_DEPTH : u8 = 3;

fn make_random_call<R: Rng + ?Sized>(rng: &mut R, depth: u8) -> FuzzOperation {
    let mut args: Vec<FuzzOperation> = Vec::new();
    for i in 0..255 {
        args.push(random_operation(rng, depth + 1, false))
    }
    FuzzOperation::Call(rng.gen(), args)
}

// FuzzOperation is potentially infinite so we'll limit the depth to something
// sensible.
fn random_operation<R: Rng + ?Sized>(rng: &mut R, depth: u8, must_call: bool) -> FuzzOperation {
    if (depth >= MAX_DEPTH) {
        return FuzzOperation::Argref(random_u8(rng));
    }

    if (must_call) {
        return make_random_call(rng, depth);
    }

    let selection = random_u8(rng);

    if selection < 5 {
        FuzzOperation::If(
            Rc::new(random_operation(rng, depth + 1, false)),
            Rc::new(random_operation(rng, depth + 1, false)),
            Rc::new(random_operation(rng, depth + 1, false))
        )
    } else if selection < 10 {
        FuzzOperation::Multiply(
            Rc::new(random_operation(rng, depth + 1, false)),
            Rc::new(random_operation(rng, depth + 1, false))
        )
    } else if selection < 20 {
        FuzzOperation::Sub(
            Rc::new(random_operation(rng, depth + 1, false)),
            Rc::new(random_operation(rng, depth + 1, false))
        )
    } else if selection < 30 {
        let mut args = Vec::new();
        let mut and_one_more: f64 = rng.gen();

        loop {
            if and_one_more > 0.5 {
                break
            }

            args.push(random_operation(rng, depth + 1, false));

            and_one_more = rng.gen();
        }

        FuzzOperation::Sha256(args)
    } else if selection < 35 {
        let mut bindings = Vec::new();
        let mut and_one_more: f64 = rng.gen();

        loop {
            bindings.push(random_operation(rng, depth + 1, false));

            if and_one_more > 0.5 {
                break
            }

            and_one_more = rng.gen();
        }

        FuzzOperation::Let(
            bindings,
            Rc::new(random_operation(rng, depth + 1, false))
        )
    } else if selection < 50 {
        make_random_call(rng, depth + 1)
    } else if selection < 60 {
        FuzzOperation::Quote(SExp::random_atom(rng))
    } else {
        FuzzOperation::Argref(random_u8(rng))
    }
}

impl Distribution<FuzzOperation> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzOperation {
        random_operation(rng, 0, false)
    }
}

fn random_arg_structure<R: Rng + ?Sized>(rng: &mut R, spine: bool) -> SExp {
    let loc = Srcloc::start(&"*rng*".to_string());
    if spine {
        if rng.gen_range(0..=1) > 0 {
            SExp::Cons(
                loc,
                Rc::new(random_arg_structure(rng, false)),
                Rc::new(random_arg_structure(rng, spine))
            )
        } else {
            SExp::Nil(loc)
        }
    } else {
        rng.gen()
    }
}

impl Distribution<ArgListType> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> ArgListType {
        match rng.gen_range(0..=1) {
            0 => ArgListType::ProperList(rng.gen_range(0..=5)),
            _ => ArgListType::Structure(random_arg_structure(rng, true))
        }
    }
}

impl ArgListType {
    fn random_args<R: Rng + ?Sized>(&self, rng: &mut R) -> SExp {
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
                            &random_vector_of::<u8, R>(rng, false)
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
                let arg_a = ArgListType::Structure(aclone).random_args(rng);
                let arg_b = ArgListType::Structure(bclone).random_args(rng);
                SExp::Cons(l.clone(), Rc::new(arg_a), Rc::new(arg_b))
            },
            ArgListType::Structure(x) => rng.gen()
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
            inline: rng.gen(),
            number: 0,
            args: rng.gen(),
            body: rng.gen()
        }
    }
}

impl FuzzFunction {
    fn to_sexp(&self, fun: &FuzzProgram) -> SExp {
        let fuzzloc = Srcloc::start(&"*fuzz*".to_string());
        let initial_atom =
            if self.inline {
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
        let body_sexp = self.body.to_sexp(&self.to_program(fun), &Vec::new(), true);
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
        let funs = random_vector_of::<FuzzFunction, R>(rng, true).iter().enumerate().map(|(i, f)| {
            let mut fcopy = f.clone();
            fcopy.number = i as u8;
            fcopy
        }).collect();

        FuzzProgram {
            args: rng.gen(),
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
            match argres.and_then(|argres| {
                let name_u8 = argres.0.as_bytes().to_vec();
                args.get(&name_u8)
            }) {
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
                let new_prog_i = replace_args(&prog_with_i, args, bindings)?;
                new_inputs.push(new_prog_i);
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

fn do_subtract(prog: &FuzzProgram, a: &FuzzOperation, b: &FuzzOperation) -> Result<FuzzOperation, RunFailure> {
    let loc = Srcloc::start(&"*err*".to_string());
    match (a, b) {
        (FuzzOperation::Quote(a), FuzzOperation::Quote(b)) => {
            let a_num = a.get_number().map_err(|e| RunFailure::RunErr(e.0, e.1))?;
            let b_num = b.get_number().map_err(|e| RunFailure::RunErr(e.0, e.1))?;
            Ok(FuzzOperation::Quote(SExp::Integer(loc, (a_num - b_num).clone())))
        },
        _ => {
            Err(RunFailure::RunErr(loc, format!("error subtracting {:?} from {:?}", b, a)))
        }
    }
}

fn do_multiply(prog: &FuzzProgram, a: &FuzzOperation, b: &FuzzOperation) -> Result<FuzzOperation, RunFailure> {
    let loc = Srcloc::start(&"*err*".to_string());
    match (a, b) {
        (FuzzOperation::Quote(a), FuzzOperation::Quote(b)) => {
            let a_num = a.get_number().map_err(|e| RunFailure::RunErr(e.0, e.1))?;
            let b_num = b.get_number().map_err(|e| RunFailure::RunErr(e.0, e.1))?;
            Ok(FuzzOperation::Quote(SExp::Integer(loc, (a_num * b_num).clone())))
        },
        _ => {
            Err(RunFailure::RunErr(loc, format!("error subtracting {:?} from {:?}", b, a)))
        }
    }
}

fn match_quote(op: &FuzzOperation) -> Result<FuzzOperation, FuzzOperation> {
    match op {
        FuzzOperation::Quote(_) => Ok(op.clone()),
        _ => Err(op.clone())
    }
}

fn match_sexp(op: &FuzzOperation) -> Result<SExp, FuzzOperation> {
    match op {
        FuzzOperation::Quote(s) => Ok(s.clone()),
        _ => Err(op.clone())
    }
}

impl FuzzProgram {
    pub fn to_sexp(&self) -> SExp {
        let mut body_vec = Vec::new();
        body_vec.push(self.args.to_sexp());
        for f in &self.functions {
            body_vec.push(f.to_sexp(self))
        }
        body_vec.push(self.body.to_sexp(self, &Vec::new(), true));
        make_operator("mod".to_string(), body_vec)
    }

    pub fn with_exp(&self, exp: &FuzzOperation) -> FuzzProgram {
        FuzzProgram {
            args: self.args.clone(),
            functions: self.functions.clone(),
            body: exp.clone()
        }
    }

    pub fn random_args<R: Rng + ?Sized>(&self, rng: &mut R) -> SExp {
        let srcloc = Srcloc::start(&"*args*".to_string());
        random_args(rng, srcloc, self.args.clone())
    }

    pub fn select_function(&self, n: u8) -> FuzzFunction {
        self.functions[n as usize % self.functions.len()].clone()
    }

    pub fn interpret_op(&self, args: &ArgInputs, bindings: &Vec<Vec<FuzzOperation>>) -> Result<FuzzOperation, RunFailure> {
        match match_quote(&self.body) {
            Ok(v) => return Ok(self.body.clone()),
            Err(v) => { }
        }

        let srcloc = Srcloc::start(&"*interp*".to_string());
        let mut assignment_map = HashMap::new();

        let prog_args_sexp =
            match args {
                ArgInputs::List(v) => {
                    let mut accum = SExp::Nil(srcloc.clone());
                    for i_reverse in 0..v.len() {
                        let i = v.len() - i_reverse - 1;
                        accum = SExp::Cons(
                            srcloc.clone(),
                            Rc::new(v[i].to_sexp(self, &Vec::new(), false)),
                            Rc::new(accum)
                        );
                    }
                    accum
                },
                ArgInputs::Atom(f) => {
                    f.to_sexp(self, &Vec::new(), false)
                },
                ArgInputs::Cons(a,b) => {
                    SExp::Cons(
                        srcloc.clone(),
                        Rc::new(a.to_sexp(self, &Vec::new(), false)),
                        Rc::new(b.to_sexp(self, &Vec::new(), false))
                    )
                }
            };

        make_assignments(Rc::new(self.args.to_sexp()), Ok(prog_args_sexp), &mut assignment_map);
        let translated_expr = replace_args(self, &assignment_map, &Vec::new())?;
        match &translated_expr {
            FuzzOperation::Quote(x) => {
                Ok(translated_expr.clone())
            },
            FuzzOperation::Argref(n) => {
                Ok(translated_expr.clone())
            },
            FuzzOperation::Call(n,call_args) => {
                let function = self.select_function(*n);
                let use_args = distribute_args(&function.args, &function.to_program(self), bindings, &call_args, &|arg| {
                    let arg_prog = self.with_exp(&arg);
                    arg_prog.interpret_op(args, bindings).unwrap_or_else(|_| arg.clone())
                }, 0);
                let prog = FuzzProgram {
                    args: function.args.clone(),
                    functions: self.functions.clone(),
                    body: function.body.clone()
                }.interpret_op(&ArgInputs::Atom(FuzzOperation::Quote(use_args.1.clone())), &Vec::new())?;
                Ok(prog)
            },
            FuzzOperation::Sub(a,b) => {
                let interpreted_a = self.with_exp(a).interpret_op(args, bindings)?;
                let interpreted_b = self.with_exp(b).interpret_op(args, bindings)?;
                do_subtract(self, &interpreted_a, &interpreted_b)
            },
            FuzzOperation::Multiply(a,b) => {
                let interpreted_a = self.with_exp(a).interpret_op(args, bindings)?;
                let interpreted_b = self.with_exp(b).interpret_op(args, bindings)?;
                do_multiply(self, &interpreted_a, &interpreted_b)
            },
            FuzzOperation::Sha256(vals) => {
                let mut hasher = sha2::Sha256::new();
                for v in vals.iter() {
                    let interpreted_v = self.with_exp(v).interpret_op(args, bindings)?;
                    match interpreted_v {
                        FuzzOperation::Quote(SExp::Atom(_,v)) => {
                            hasher.update(v);
                        },
                        FuzzOperation::Quote(SExp::Integer(_,i)) => {
                            let int_bytes = bigint_to_bytes(&i, Some(TConvertOption { signed: true })).unwrap().data().to_vec();
                            hasher.update(int_bytes);
                        },
                        _ => {
                            return Err(RunFailure::RunErr(srcloc, format!("Uninterpreted {} in sha256", interpreted_v.to_sexp(self, &Vec::new(), true).to_string())));
                        }
                    }
                }
                let hash_result = hasher.finalize();
                Ok(FuzzOperation::Quote(SExp::Atom(srcloc.clone(), hash_result.to_vec())))
            },
            FuzzOperation::If(cond, dothen, doelse) => {
                let interpreted_cond = match_sexp(&self.with_exp(cond).interpret_op(args, bindings)?).map_err(|e| RunFailure::RunErr(srcloc.clone(), format!("uninterpreted {} in if", e.to_sexp(self, &Vec::new(), true).to_string())))?;
                if truthy(Rc::new(interpreted_cond.clone())) {
                    self.with_exp(dothen).interpret_op(args, bindings)
                } else {
                    self.with_exp(doelse).interpret_op(args, bindings)
                }
            },
            _ => {
                Err(RunFailure::RunErr(srcloc, format!("Don't know how to interpret {} {:?}", translated_expr.to_sexp(self, &Vec::new(), true).to_string(), translated_expr)))
            }
        }
    }

    pub fn interpret(&self, args: Rc<SExp>) -> Result<SExp, RunFailure> {
        let arginputs =
            match args.borrow() {
                SExp::Cons(l,h,t) => {
                    let h_borrow: &SExp = h.borrow();
                    let t_borrow: &SExp = t.borrow();
                    ArgInputs::Cons(
                        FuzzOperation::Quote(h_borrow.clone()),
                        FuzzOperation::Quote(t_borrow.clone())
                    )
                },
                _ => {
                    let a_borrow: &SExp = args.borrow();
                    ArgInputs::Atom(FuzzOperation::Quote(a_borrow.clone()))
                }
            };

        let result = self.interpret_op(&arginputs, &Vec::new())?;
        Ok(result.to_sexp(self, &Vec::new(), true))
    }
}

pub fn rng_from_string(v: String) -> SmallRng {
    let mut init_vec: [u8; 32] = Default::default();
    let init_bytes = v.as_bytes();
    for i in 0..32 {
        init_vec[i] = init_bytes[i%init_bytes.len()];
    }
    SmallRng::from_seed(init_vec)
}

#[test]
fn try_subtract_simple() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result = FuzzOperation::Quote(SExp::Atom(loc.clone(), vec!(1)));
    let a = FuzzOperation::Quote(SExp::Atom(loc.clone(), vec!(43)));
    let b = FuzzOperation::Quote(SExp::Atom(loc.clone(), vec!(42)));
    let prog = FuzzProgram {
        args: ArgListType::ProperList(0),
        functions: Vec::new(),
        body: FuzzOperation::Sub(Rc::new(a.clone()), Rc::new(b.clone()))
    };
    assert_eq!(Ok(result), do_subtract(&prog, &a, &b));
}

#[test]
fn try_interp_simple_subtraction() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result = fuzz_num(1);
    let prog = FuzzProgram {
        args: ArgListType::ProperList(2),
        functions: Vec::new(),
        body: FuzzOperation::Sub(Rc::new(FuzzOperation::Argref(0)), Rc::new(FuzzOperation::Argref(1)))
    };
    let args = ArgInputs::List(vec!(fuzz_num(100), fuzz_num(99)));
    assert_eq!(Ok(result), prog.interpret_op(&args, &Vec::new()));
}

#[test]
fn try_interp_simple_sha256() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result = FuzzOperation::Quote(SExp::Atom(loc.clone(), vec!(
        0x78, 0x53, 0xe8, 0x85, 0x6e, 0x95, 0xcd, 0xad,
        0x7c, 0xea, 0x9b, 0x99, 0xeb, 0x08, 0xd7, 0xac,
        0xf4, 0x02, 0x20, 0x4e, 0x63, 0xa8, 0x3c, 0x67,
        0x2e, 0xa6, 0x17, 0x49, 0x28, 0x16, 0x66, 0x0d,
    )));
    let prog = FuzzProgram {
        args: ArgListType::ProperList(2),
        functions: Vec::new(),
        body: FuzzOperation::Sha256(vec!(FuzzOperation::Argref(0), FuzzOperation::Argref(1)))
    };
    let args = ArgInputs::List(vec!(fuzz_num(19), fuzz_num(23)));
    assert_eq!(Ok(result), prog.interpret_op(&args, &Vec::new()));
}

#[test]
fn try_interp_simple_sha256_and_sub() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result = FuzzOperation::Quote(SExp::Atom(loc.clone(), vec!(
        0x98, 0x72, 0x2e, 0x2e, 0xbe, 0xd8, 0xed, 0x3d,
        0x36, 0x52, 0xe1, 0x1e, 0x41, 0x81, 0xf0, 0xdc,
        0xcc, 0x1c, 0xe7, 0xd1, 0x92, 0xd8, 0xf1, 0xdb,
        0x37, 0x0a, 0xf8, 0xec, 0x4a, 0x4e, 0x17, 0x4a,
    )));
    let prog = FuzzProgram {
        args: ArgListType::ProperList(2),
        functions: Vec::new(),
        body: FuzzOperation::Sha256(vec!(FuzzOperation::Sub(Rc::new(FuzzOperation::Argref(0)), Rc::new(FuzzOperation::Argref(1)))))
    };
    let args = ArgInputs::List(vec!(fuzz_num(19), fuzz_num(23)));
    assert_eq!(Ok(result), prog.interpret_op(&args, &Vec::new()));
}

#[test]
fn try_interp_simple_sha256_and_sub_with_fun() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result = FuzzOperation::Quote(SExp::Atom(loc.clone(), vec!(
        0x98, 0x72, 0x2e, 0x2e, 0xbe, 0xd8, 0xed, 0x3d,
        0x36, 0x52, 0xe1, 0x1e, 0x41, 0x81, 0xf0, 0xdc,
        0xcc, 0x1c, 0xe7, 0xd1, 0x92, 0xd8, 0xf1, 0xdb,
        0x37, 0x0a, 0xf8, 0xec, 0x4a, 0x4e, 0x17, 0x4a,
    )));
    let prog = FuzzProgram {
        args: ArgListType::ProperList(2),
        functions: vec!(FuzzFunction {
            inline: false,
            number: 0,
            args: ArgListType::ProperList(2),
            body: FuzzOperation::Sub(Rc::new(FuzzOperation::Argref(0)), Rc::new(FuzzOperation::Argref(1)))
        }),
        body: FuzzOperation::Sha256(vec!(FuzzOperation::Call(0, vec!(FuzzOperation::Argref(0), FuzzOperation::Argref(1)))))
    };
    let args = ArgInputs::List(vec!(fuzz_num(19), fuzz_num(23)));
    assert_eq!(Ok(result), prog.interpret_op(&args, &Vec::new()));
}

#[test]
fn try_interp_simple_sha256_and_sub_with_fun_arg_swap_1() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result = FuzzOperation::Quote(SExp::Atom(loc.clone(), vec!(
        0x98, 0x72, 0x2e, 0x2e, 0xbe, 0xd8, 0xed, 0x3d,
        0x36, 0x52, 0xe1, 0x1e, 0x41, 0x81, 0xf0, 0xdc,
        0xcc, 0x1c, 0xe7, 0xd1, 0x92, 0xd8, 0xf1, 0xdb,
        0x37, 0x0a, 0xf8, 0xec, 0x4a, 0x4e, 0x17, 0x4a,
    )));
    let prog = FuzzProgram {
        args: ArgListType::ProperList(2),
        functions: vec!(FuzzFunction {
            inline: false,
            number: 0,
            args: ArgListType::ProperList(2),
            body: FuzzOperation::Sub(Rc::new(FuzzOperation::Argref(0)), Rc::new(FuzzOperation::Argref(1)))
        }),
        body: FuzzOperation::Sha256(vec!(FuzzOperation::Call(0, vec!(FuzzOperation::Argref(1), FuzzOperation::Argref(0)))))
    };
    let args = ArgInputs::List(vec!(fuzz_num(23), fuzz_num(19)));
    assert_eq!(Ok(result), prog.interpret_op(&args, &Vec::new()));
}

#[test]
fn try_interp_simple_sha256_and_sub_with_fun_arg_swap_2() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result = FuzzOperation::Quote(SExp::Atom(loc.clone(), vec!(
        0x98, 0x72, 0x2e, 0x2e, 0xbe, 0xd8, 0xed, 0x3d,
        0x36, 0x52, 0xe1, 0x1e, 0x41, 0x81, 0xf0, 0xdc,
        0xcc, 0x1c, 0xe7, 0xd1, 0x92, 0xd8, 0xf1, 0xdb,
        0x37, 0x0a, 0xf8, 0xec, 0x4a, 0x4e, 0x17, 0x4a,
    )));
    let prog = FuzzProgram {
        args: ArgListType::ProperList(2),
        functions: vec!(FuzzFunction {
            inline: false,
            number: 0,
            args: ArgListType::ProperList(2),
            body: FuzzOperation::Sub(Rc::new(FuzzOperation::Argref(1)), Rc::new(FuzzOperation::Argref(0)))
        }),
        body: FuzzOperation::Sha256(vec!(FuzzOperation::Call(0, vec!(FuzzOperation::Argref(0), FuzzOperation::Argref(1)))))
    };
    let args = ArgInputs::List(vec!(fuzz_num(23), fuzz_num(19)));
    assert_eq!(Ok(result), prog.interpret_op(&args, &Vec::new()));
}

#[test]
fn try_interp_simple_sha256_and_sub_with_fun_arg_swap_diff_args() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result = FuzzOperation::Quote(SExp::Integer(loc.clone(), 8_i32.to_bigint().unwrap()));
    let prog = FuzzProgram {
        args: ArgListType::ProperList(2),
        functions: vec!(FuzzFunction {
            inline: false,
            number: 0,
            args: ArgListType::ProperList(3),
            body: FuzzOperation::Multiply(
                Rc::new(FuzzOperation::Sub(
                    Rc::new(FuzzOperation::Argref(0)),
                    Rc::new(FuzzOperation::Argref(1))
                )),
                Rc::new(FuzzOperation::Argref(2))
            )
        }),
        body: FuzzOperation::Call(0, vec!(
            FuzzOperation::Argref(0),
            FuzzOperation::Argref(1),
            fuzz_num(2)
        ))
    };
    let args = ArgInputs::List(vec!(fuzz_num(23), fuzz_num(19)));
    assert_eq!(Ok(result), prog.interpret_op(&args, &Vec::new()));
}

#[test]
fn try_interp_simple_if_1() {
    let loc = Srcloc::start(&"*test*".to_string());

    let prog = FuzzProgram {
        args: ArgListType::ProperList(3),
        functions: Vec::new(),
        body: FuzzOperation::If(
            Rc::new(FuzzOperation::Argref(0)),
            Rc::new(FuzzOperation::Argref(1)),
            Rc::new(FuzzOperation::Argref(2))
        )
    };
    let args_false = ArgInputs::List(vec!(fuzz_num(0), fuzz_num(23), fuzz_num(19)));
    let args_true = ArgInputs::List(vec!(fuzz_num(1), fuzz_num(23), fuzz_num(19)));

    assert_eq!(Ok(fuzz_num(19)), prog.interpret_op(&args_false, &Vec::new()));
    assert_eq!(Ok(fuzz_num(23)), prog.interpret_op(&args_true, &Vec::new()));
}

#[test]
fn try_destructured_args_1() {
    let loc = Srcloc::start(&"*test*".to_string());

    let prog = FuzzProgram {
        args: ArgListType::Structure(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::atom_from_string(loc.clone(), &"a1".to_string())),
            Rc::new(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::atom_from_string(loc.clone(), &"b1".to_string())),
                    Rc::new(SExp::atom_from_string(loc.clone(), &"b2".to_string()))
                )),
                Rc::new(SExp::Nil(loc.clone()))
            ))
        )),
        functions: Vec::new(),
        body: FuzzOperation::Sha256(vec!(
            FuzzOperation::Argref(0),
            FuzzOperation::Argref(1),
            FuzzOperation::Argref(2))
        )
    };

    let interp_args = ArgInputs::List(vec!(
        fuzz_num(1234),
        FuzzOperation::Quote(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::Integer(loc.clone(), 5678_i32.to_bigint().unwrap())),
            Rc::new(SExp::Integer(loc.clone(), 9101112_i32.to_bigint().unwrap()))
        ))
    ));

    let result = FuzzOperation::Quote(SExp::Atom(loc.clone(), vec!(
        0xfa, 0x4e, 0x77, 0x0a, 0xa0, 0x40, 0xd7, 0x2c,
        0xc0, 0x83, 0x3c, 0x81, 0x26, 0x9b, 0xf2, 0x68,
        0x86, 0x77, 0x8c, 0xd9, 0x65, 0xc3, 0x62, 0x3a,
        0x93, 0xfa, 0x5d, 0xa9, 0x49, 0x0b, 0x52, 0xfc,
    )));

    assert_eq!(Ok(result), prog.interpret_op(&interp_args, &Vec::new()));
}

#[test]
fn try_destructured_args_2() {
    let loc = Srcloc::start(&"*test*".to_string());

    let prog = FuzzProgram {
        args: ArgListType::ProperList(0),
        functions: vec!(FuzzFunction {
            inline: false,
            number: 0,
            args: ArgListType::Structure(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::atom_from_string(loc.clone(), &"a1".to_string())),
                Rc::new(SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::Cons(
                        loc.clone(),
                        Rc::new(SExp::atom_from_string(loc.clone(), &"b1".to_string())),
                        Rc::new(SExp::atom_from_string(loc.clone(), &"b2".to_string()))
                    )),
                    Rc::new(SExp::Nil(loc.clone()))
                ))
            )),
            body: FuzzOperation::Sha256(vec!(
                FuzzOperation::Argref(0),
                FuzzOperation::Argref(1),
                FuzzOperation::Argref(2))
            )
        }),
        body: FuzzOperation::Call(0, vec!(
            fuzz_num(1234),
            fuzz_num(5678),
            fuzz_num(9101112),
            fuzz_num(0)
        ))
    };

    let result = FuzzOperation::Quote(SExp::Atom(loc.clone(), vec!(
        0xfa, 0x4e, 0x77, 0x0a, 0xa0, 0x40, 0xd7, 0x2c,
        0xc0, 0x83, 0x3c, 0x81, 0x26, 0x9b, 0xf2, 0x68,
        0x86, 0x77, 0x8c, 0xd9, 0x65, 0xc3, 0x62, 0x3a,
        0x93, 0xfa, 0x5d, 0xa9, 0x49, 0x0b, 0x52, 0xfc,
    )));

    assert_eq!(Ok(result), prog.interpret_op(&ArgInputs::List(Vec::new()), &Vec::new()));
}

#[test]
// prog: (mod m (defun-inline fun_0 (arg_1 arg_2 arg_3 arg_4 arg_5) arg_3) (fun_0 m m (let ((binding_0 m)) binding_0) m m))
// args: 6682899131939974478
// => 6682899131939974478
fn try_destructured_args_3() {
    let loc = Srcloc::start(&"*test*".to_string());
    let prog = FuzzProgram {
        args: ArgListType::Structure(SExp::atom_from_string(loc.clone(), &"m".to_string())),
        functions: vec!(FuzzFunction {
            inline: true,
            number: 0,
            args: ArgListType::ProperList(5),
            body: FuzzOperation::Argref(2)
        }),
        body: FuzzOperation::Call(0, vec!(
            FuzzOperation::Argref(0),
            FuzzOperation::Argref(0),
            FuzzOperation::Let(vec!(FuzzOperation::Argref(0)), Rc::new(FuzzOperation::Argref(1))),
            FuzzOperation::Argref(0),
            FuzzOperation::Argref(0)
        ))
    };

    let test_num_rc = parse_sexp(loc.clone(), &"6682899131939974478".to_string()).unwrap()[0].clone();
    let test_num: &SExp = test_num_rc.borrow();
    let fuzz_num = FuzzOperation::Quote(test_num.clone());
    let args = ArgInputs::Atom(fuzz_num.clone());
    assert_eq!(Ok(fuzz_num), prog.interpret_op(&args, &Vec::new()));
}
