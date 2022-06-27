use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::env;
use std::rc::Rc;

use clvm_tools_rs::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    sha256
};
use clvm_tools_rs::compiler::clvm::{sha256tree, truthy};
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

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum ClvmExecutionStep {
    Untreated(Rc<SExp>),
    Exception(Rc<SExp>),
    Constant(Rc<SExp>),
    EnvRef(Path),
    PrimitiveOp(u8, Vec<Path>),
    CallProgram(Vec<u8>, Rc<SExp>, Path), // clvm-code, env-path
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum Hash {
    Sha256Hash(Vec<u8>)
}

impl Hash {
    pub fn is_empty(&self) -> bool {
        match self {
            Hash::Sha256Hash(v) => v.is_empty()
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum Path {
    Value(Vec<u8>)
}

impl Path {
    fn len(&self) -> usize {
        match self {
            Path::Value(v) => v.len()
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum MessageType<T,R> {
    Request(T),
    Reply(R)
}

trait ProcessQueue<T,R> {
    fn get_self(&self) -> u32;
    fn read(&mut self) -> Option<MessageType<T,R>>;
    fn reply(&mut self, target: u32, value: R);
    fn forward(&mut self, target: u32, r: T);
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct RunRequest {
    code: Rc<SExp>,
    env: Rc<SExp>,
    replyto: u32,
    treehash: Hash,
    envhash: Hash
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct RunReply {
    treehash: Hash,
    envhash: Hash,
    result: Result<Rc<SExp>, Rc<SExp>>
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum ProgramAndEnvHash {
    Value(Hash, Hash)
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum HashesAndPath {
    Value(Hash, Hash, Path)
}

fn insert_primop(
    runmap: &mut HashMap<HashesAndPath, ClvmExecutionStep>,
    path: Path,
    operator: Vec<u8>,
    alist: Vec<SExp>
) {
    todo!("not implemented yet");
    // Replace with PrimitveOp

    // First iterate and insert argument computations

    // Next insert the operation itself.
}

fn choose_env(path: Path, sexp: Rc<SExp>) -> ClvmExecutionStep {
    todo!("not today");
}

fn copy_to_runmap(target: &mut HashMap<HashesAndPath, ClvmExecutionStep>, src: &HashMap<HashesAndPath, ClvmExecutionStep>) {
    for kv in src.iter() {
        target.insert(kv.0.clone(), kv.1.clone());
    }
}

fn make_exn_tail_list(loc: &Srcloc, l: Vec<Rc<SExp>>) -> Rc<SExp> {
    let mut res = Rc::new(SExp::Nil(loc.clone()));
    for i_reverse in 0..l.len() {
        let i = l.len() - i_reverse - 1;
        res = Rc::new(SExp::Cons(loc.clone(), l[i].clone(), res));
    }
    res
}

// How to execute CLVM in temporal logic
// A program is a set of path to invocation mappings
// Each invocation contains an operation to perform and a
// list of paths to resolve
// In order to function, we must be able to start resolving in the first step
// NamedReference -> Constant
// If all paths satisfied:
// PrimitiveOp ->
//   if apply
//     perform treehash of program
//     produce CallProgram
//   else if not apply
//     replace with Constant
// CallProgram ->
//   enqueue clvm call with path as key
fn executeclvm(runners: HashMap<Hash, u32>, readable: &mut dyn ProcessQueue<RunRequest, RunReply>) {
    let mut computed: HashMap<ProgramAndEnvHash, ClvmExecutionStep> = HashMap::new();
    let mut runmap: HashMap<HashesAndPath, ClvmExecutionStep> = HashMap::new();
    let mut requested: HashSet<ProgramAndEnvHash> = HashSet::new();
    let mut requests: HashMap<ProgramAndEnvHash, RunRequest> = HashMap::new();
    let /*mut*/ runners: HashMap<Hash, u32> = HashMap::new();

    loop {
        // Dequeue a request
        let msg = readable.read();
        let mut new_runmap = HashMap::new();

        // Bring in new request if received
        if let Some(MessageType::Request(req_)) = msg {
            // Compute hashes if needed
            let mut req = req_.clone();
            if req.treehash.is_empty() {
                req.treehash = Hash::Sha256Hash(sha256tree(req.code.clone()));
            }
            if req.envhash.is_empty() {
                req.envhash = Hash::Sha256Hash(sha256tree(req.env.clone()));
            }

            // Check for already run
            if let Some(precomputed) = computed.get(&ProgramAndEnvHash::Value(req.treehash.clone(), req.envhash.clone())) {
                let rval =
                    match precomputed {
                        ClvmExecutionStep::Constant(pc) => Ok(pc.clone()),
                        ClvmExecutionStep::Exception(e) => Err(e.clone()),
                        _ => panic!("can't handle it")
                    };

                readable.reply(req.replyto, RunReply {
                    treehash: req.treehash.clone(),
                    envhash: req.envhash.clone(),
                    result: rval
                });

                continue;
            }

            if let Some(target_runner) = runners.get(&req.treehash) {
                readable.forward(*target_runner, req.clone());
                continue;
            }

            // Turn into paths and evaluations
            requests.insert(ProgramAndEnvHash::Value(req.treehash.clone(), req.envhash.clone()), req.clone());
            runmap.insert(HashesAndPath::Value(req.treehash.clone(), req.envhash.clone(), Path::Value(vec![1])), ClvmExecutionStep::Untreated(req.code.clone()));
        } else if let Some(MessageType::Reply(rep)) = msg {
            // Bring in new reply if received
            let res =
                rep.result.
                map(|v| ClvmExecutionStep::Constant(v.clone())).
                unwrap_or_else(|e| ClvmExecutionStep::Exception(e.clone()));
            computed.insert(ProgramAndEnvHash::Value(rep.treehash, rep.envhash), res);
        }

        for kv in runmap.iter() {
            match (kv.0, kv.1) {
                (HashesAndPath::Value(codehash, envhash, path), ClvmExecutionStep::Untreated(code)) => {
                    match code.borrow() {
                        SExp::Atom(_,v) => {
                            new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), Path::Value(vec![1])), ClvmExecutionStep::EnvRef(Path::Value(v.clone())));
                        },
                        SExp::Nil(_) => {
                            new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), Path::Value(vec![1])), ClvmExecutionStep::Constant(code.clone()));
                        },
                        SExp::Cons(_,a,b) => {
                            if let Some(lst) = code.proper_list() {
                                if let SExp::Atom(_,pname) = lst[0].borrow() {
                                    if pname.len() == 1 && pname[0] == 1 {
                                        // Quoted
                                        new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), path.clone()), ClvmExecutionStep::Constant(b.clone()));
                                    } else {
                                        insert_primop(&mut new_runmap, path.clone(), pname.clone(), lst);
                                    }
                                } else {
                                    // Error: head should be an atom
                                    new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), Path::Value(vec![1])), ClvmExecutionStep::Exception(code.clone()));
                                }
                            } else {
                                // Error: all prims use a proper list
                                new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), Path::Value(vec![1])), ClvmExecutionStep::Exception(code.clone()));
                            }
                        },
                        _ => todo!("implement other cases")
                    }
                },
                (HashesAndPath::Value(codehash, envhash, path), ClvmExecutionStep::Constant(c)) => {
                    if path == &Path::Value(vec![1]) {
                        let identifier = ProgramAndEnvHash::Value(codehash.clone(), envhash.clone());
                        // Cache
                        computed.insert(identifier.clone(), ClvmExecutionStep::Constant(c.clone()));
                        if let Some(req) = requests.get(&identifier) {
                            // Reply that the run completed.
                            readable.reply(req.replyto, RunReply {
                                treehash: codehash.clone(),
                                envhash: envhash.clone(),
                                result: Ok(c.clone())
                            });
                        }
                    }
                },
                (HashesAndPath::Value(codehash, envhash, path), ClvmExecutionStep::Exception(x)) => {
                    // Propogate an exception
                    new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), Path::Value(vec![1])), ClvmExecutionStep::Exception(x.clone()));
                },
                (HashesAndPath::Value(codehash, envhash, path), ClvmExecutionStep::EnvRef(epath)) => {
                    // Make a path choice
                    if let Some(req) = requests.get(&ProgramAndEnvHash::Value(codehash.clone(), envhash.clone())) {
                        new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), path.clone()), choose_env(epath.clone(), req.env.clone()));
                    }
                },
                (HashesAndPath::Value(codehash, envhash, path), ClvmExecutionStep::PrimitiveOp(op, paths)) => {
                    let mut constant_inputs = Vec::new();
                    for p in paths.iter() {
                        if let Some(ClvmExecutionStep::Constant(c)) = runmap.get(&HashesAndPath::Value(codehash.clone(), envhash.clone(), p.clone())) {
                            constant_inputs.push(c.clone());
                        }
                    }

                    if constant_inputs.len() == path.len() {
                        // All arguments converted
                        match op {
                            2 => {
                                // Apply
                                // Enqueue a new request to ourselves.
                                let reqid = ProgramAndEnvHash::Value(codehash.clone(), envhash.clone());

                                if let Some(result) = computed.get(&reqid) {
                                    new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), path.clone()), result.clone());
                                } else if !requested.contains(&reqid) {
                                    requested.insert(reqid);
                                    readable.forward(readable.get_self(), RunRequest {
                                        code: constant_inputs[1].clone(),
                                        env: constant_inputs[2].clone(),
                                        replyto: readable.get_self(),
                                        treehash: Hash::Sha256Hash(sha256tree(constant_inputs[1].clone())),
                                        envhash: Hash::Sha256Hash(sha256tree(constant_inputs[2].clone()))
                                    });
                                }
                            },
                            3 => {
                                // Condition
                                let new_value =
                                    if truthy(constant_inputs[1].clone()) {
                                        constant_inputs[2].clone()
                                    } else {
                                        constant_inputs[3].clone()
                                    };
                                new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), path.clone()), ClvmExecutionStep::Constant(new_value));
                            },
                            4 => {
                                // Cons
                                new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), path.clone()), ClvmExecutionStep::Constant(Rc::new(SExp::Cons(constant_inputs[1].loc(), constant_inputs[2].clone(), constant_inputs[3].clone()))));
                            },
                            5 => {
                                // First
                                let id = HashesAndPath::Value(codehash.clone(), envhash.clone(), path.clone());
                                let value =
                                    if let SExp::Cons(_,a,_) = constant_inputs[1].borrow() {
                                        ClvmExecutionStep::Constant(a.clone())
                                    } else {
                                        ClvmExecutionStep::Exception(constant_inputs[1].clone())
                                    };
                                new_runmap.insert(id, value);
                            },
                            6 => {
                                // Rest
                                let id = HashesAndPath::Value(codehash.clone(), envhash.clone(), path.clone());
                                let value =
                                    if let SExp::Cons(_,_,b) = constant_inputs[1].borrow() {
                                        ClvmExecutionStep::Constant(b.clone())
                                    } else {
                                        ClvmExecutionStep::Exception(constant_inputs[1].clone())
                                    };
                                new_runmap.insert(id, value);
                            },
                            7 => {
                                // isList
                                let result =
                                    if let SExp::Cons(l,_,_) = constant_inputs[1].borrow() {
                                        Rc::new(SExp::Atom(l.clone(), vec![1]))
                                    } else {
                                        Rc::new(SExp::Nil(constant_inputs[1].loc()))
                                    };
                                new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), path.clone()), ClvmExecutionStep::Constant(result));
                            },
                            8 => {
                                // Exn
                                let loc = Srcloc::start(&"*exn*".to_string());
                                new_runmap.insert(HashesAndPath::Value(codehash.clone(), envhash.clone(), Path::Value(vec![1])), ClvmExecutionStep::Exception(make_exn_tail_list(&loc, constant_inputs)));
                            },
                            _ => {
                                // Unknown
                                todo!("don't know this op");
                            },
                        }
                    }
                },
                _ => todo!("handle other cases (probably empty)")
            }
        }

        copy_to_runmap(&mut runmap, &new_runmap);
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
