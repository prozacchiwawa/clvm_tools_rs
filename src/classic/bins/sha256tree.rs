use std::borrow::Borrow;
use std::env;
use std::rc::Rc;

use clvm_tools_rs::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    sha256
};
use clvm_tools_rs::compiler::clvm::sha256tree;
use clvm_tools_rs::compiler::sexp::{SExp, parse_sexp};
use clvm_tools_rs::compiler::srcloc::Srcloc;
use clvm_tools_rs::util::u8_from_number;

#[derive(Debug, Clone)]
enum HashState {
    Untreated(Rc<SExp>),
    Collect,
    Hashing(Vec<u8>),
    Hashed(Vec<u8>)
}

fn is_finished(x: &HashState) -> bool {
    match x {
        HashState::Hashed(v) => true,
        _ => false
    }
}

// Atom[A] -> Hashing[1,A]
// Cons[A,B] -> Collect, Hashed[A], Hashed[B]
// Hashing[1,A] + result[X] -> Hashed[X]
// Collect, Hashed[A], Hashed[B] -> Hashing[2,A,B]
fn sha256steps(s: Rc<SExp>) -> Vec<u8> {
    let mut work: Vec<HashState> = Vec::new();
    let mut vqueue: Vec<(Vec<u8>,Vec<u8>)> = Vec::new();
    let mut shaqueue = Vec::new();

    work.push(HashState::Untreated(s.clone()));

    while !is_finished(&work[0]) {
        let mut i = 0;
        if let Some((orig,hash)) = vqueue.pop() {
            i = 0;
            while i < work.len() {
                let workitem = work[i].clone();
                if let HashState::Hashing(a) = workitem {
                    if a == orig {
                        work[i] = HashState::Hashed(hash.clone());
                    }
                }
                i += 1;
            }
        }

        i = 0;
        while i < work.len() {
            let workitem = work[i].clone();
            match workitem {
                HashState::Collect => {
                    let a = work[i+1].clone();
                    let b = work[i+2].clone();
                    if let (HashState::Hashed(a), HashState::Hashed(b)) = (a,b) {
                        work.remove(i+1);
                        work.remove(i+1);
                        let mut hashvec = vec![2];
                        hashvec.append(&mut a.clone());
                        hashvec.append(&mut b.clone());
                        work[i] = HashState::Hashing(hashvec.clone());
                        shaqueue.push(hashvec);
                    }
                },
                HashState::Untreated(sexp) => {
                    let sexp_copy = sexp.clone();
                    match sexp_copy.borrow() {
                        SExp::Nil(_) => {
                            work[i] = HashState::Hashed(vec![75, 245, 18, 47, 52, 69, 84, 197, 59, 222, 46, 187, 140, 210, 183, 227, 209, 96, 10, 214, 49, 195, 133, 165, 215, 204, 226, 60, 119, 133, 69, 154]);
                        },
                        SExp::Atom(_,a) => {
                            let mut hashvec = vec![1];
                            hashvec.append(&mut a.clone());
                            work[i] = HashState::Hashing(hashvec.clone());
                            shaqueue.push(hashvec);
                        },
                        SExp::QuotedString(l,_,s) => {
                            work[i] = HashState::Untreated(Rc::new(SExp::Atom(l.clone(),s.clone())));
                        },
                        SExp::Integer(l,ival) => {
                            work[i] = HashState::Untreated(Rc::new(SExp::Atom(l.clone(),u8_from_number(ival.clone()))));
                        },
                        SExp::Cons(l,a,b) => {
                            work[i] = HashState::Collect;
                            work.insert(i+1, HashState::Untreated(a.clone()));
                            work.insert(i+2, HashState::Untreated(b.clone()));
                        }
                    }
                },
                _ => { }
            }
            i += 1;
        }

        if let Some(sq) = shaqueue.pop() {
            let res = sha256(Bytes::new(Some(BytesFromType::Raw(sq.clone())))).data().clone();
            vqueue.push((sq, res));
        }
    }

    if let HashState::Hashed(x) = &work[0] {
        return x.clone();
    } else {
        panic!("could not treehash");
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let loc = Srcloc::start(&"*program*".to_string());
    if args.len() < 2 {
        eprintln!("give a clvm value to sha256tree");
        return;
    }
    parse_sexp(loc.clone(), &args[1])
        .map_err(|e| {
            println!("{}: {}", e.0.to_string(), e.1.clone());
        })
        .map(|p| {
            let shanew = sha256steps(p[0].clone());
            let shaold = sha256tree(p[0].clone());
            if shanew != shaold {
                panic!("unmatched hashes");
            }
            println!("{}", Bytes::new(Some(BytesFromType::Raw(shanew.clone()))).hex());
        });
}
