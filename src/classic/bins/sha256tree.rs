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

enum ClvmExecutionStep {
    Untreated(Rc<SExp>),
    Exception(Rc<SExp>),
    Constant(Rc<SExp>),
    EnvRef(Path),
    PrimitiveOp(u8, Vec<Path>),
    CallProgram(Vec<u8>, Rc<SExp>, Path), // clvm-code, env-path
}

enum Hash {
    Sha256Hash(Vec<u8>)
}

enum Path {
    PathInProgram(Vec<u8>)
}

enum MessageType<T,R> {
    Request<T>,
    Reply<R>
}

trait<T,R> ProcessQueue<T,R> {
    fn get_self() -> u32;
    fn read(&mut self) -> Option<MessageType<T,R>>;
    fn reply(&mut self, u32 target, value: R);
    fn forward(&mut self, u32 target, r: T);
}

enum RunRequest {
    code: Rc<SExp>,
    env: Rc<SExp>,
    replyto: u32,
    treehash: Hash,
    envhash: Hash
}

enum RunReply {
    treehash: Hash,
    envhash: Hash,
    result: Error<Rc<SExp>, Rc<SExp>>
}

enum ProgramAndEnvHash {
    ProgramAndEnvHash(Hash, Hash)
}

enum HashesAndPath {
    HashesAndPath(Hash, Hash, Path)
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
    let mut computed: HashMap<ProgramAndEnvHash, Rc<SExp>> = HashMap::new();
    let mut runmap: HashMap<HashesAndPath, ClvmExecutionStep> = HashMap::new();
    let mut requested: HashSet<ProgramAndEnvHash> = HashSet::new();
    let mut requests: HashMap<ProgramAndEnvHash, RunRequest> = HashMap::new();

    loop {
        // Dequeue a request
        let mut msg = readable.read();

        // Bring in new request if received
        if let Some(MessageType::Request(req)) = msg {
            // Compute hashes if needed
            if is_empty(req.treehash) {
                req.treehash = sha256tree(req.code.clone());
            }
            if is_empty(req.envhash) {
                req.envhash = sha256tree(req.env.clone());
            }

            // Check for already run
            if let Some(precomputed) = computed.get(ProgramAndEnvHash(req.treehash, req.envhash)) {
                readable.reply(req.replyto, RunReply {
                    treehash: req.treehash.clone(),
                    envhash: req.envhash.clone(),
                    result: Ok(precomputed.clone())
                });
                continue;
            }

            if let Some(target_runner) = runners.get(req.treehash.clone()) {
                readable.forward(target_runner, req);
                continue;
            }

            // Turn into paths and evaluations
            requests.insert(ProgramAndEnvHash(req.treehash, req.envhash), req);
            runmap.insert(HashesAndPath(req.treehash, req.envhash, vec![1]), ClvmExecutionStep::Untreated(req.code));
        }

        let mut new_runmap = HashMap::new();

        // Bring in new reply if received
        if let Some(MessageType::Reply(rep)) = msg {
            let res =
                rep.result.
                map(|v| Constant(v.clone())).
                map_err(|e| Exception(e.clone()));
            computed.insert(ProgramAndEnvHash(rep.treehash, rep.envhash), rep.result);
        }

        for kv in runmap.iter() {
            match (kv.0, kv.1) {
                (HashesAndPath(codehash, envhash, path), Untreated(code)) => {
                    match code.borrow() {
                        SExp::Atom(_,v) => runmap.insert(HashesAndPath(codehash, envhash, vec![1]), EnvRef(v.clone())),
                        SExp::Nil(_) => runmap.insert(HashesAndPath(codehash, envhash, vec![1]), Constant(code.clone())),
                        SExp::Cons(_,a,b) => {
                            if let Some(lst) = proper_list(code, true) {
                                if let SExp::Atom(_,pname) = lst[0] {
                                    if pname.len() == 1 && pname[0] == 1 {
                                        // Quoted
                                        new_runmap.insert(HashesAndPath(codehash, envhash, path), Constant(b.clone()));
                                    } else {
                                        insert_primop(&mut new_runmap, path, pname, lst);
                                    }
                                } else {
                                    // Error: head should be an atom
                                    new_runmap.insert(HashesAndPath(codehash, envhash, vec![1]), Exception(code.clone()));
                                }
                            } else {
                                // Error: all prims use a proper list
                                new_runmap.insert(HashesAndPath(codehash, envhash, vec![1]), Exception(code.clone()));
                            }
                        }
                    }
                },
                (HashesAndPath(codehash, envhash, path), Constant(c)) => {
                    if path == 1 {
                        let identifier = ProgramAndEnvHash(codehash, envhash);
                        // Cache
                        computed.insert(identifier, c);
                        // Reply that the run completed.
                        readable.reply(RunReply {
                            treehash.clone(),
                            envhash.clone(),
                            Ok(c.clone())
                        });
                    }
                },
                (HashesAndPath(codehash, envhash, path), Exception(x)) => {
                    // Propogate an exception
                    new_runmap.insert(HashesAndPath(codehash, envhash, vec![1]), Exception(x.clone()));
                },
                (HashesAndPath(codehash, envhash, path), EnvRef(epath)) => {
                    // Make a path choice
                    if let Some(req) = requests.get(ProgramAndEnvHash(codehash, envhash)) {
                        new_runmap.insert(HashesAndPath(codehash, envhash, path), choose_env(epath, req.env));
                    }
                },
                (HashesAndPath(codehash, envhash, path), PrimitveOp(op, paths)) => {
                    let mut constant_inputs = Vec::new();
                    for p in paths.iter() {
                        if let Some(Constant(c)) = runmap.get(p) {
                            constant_inputs.push(c.clone());
                        }
                    }

                    if constant_inputs.len() == path.len() {
                        // All arguments converted
                        match op {
                            2 => {
                                // Apply
                                // Enqueue a new request to ourselves.
                                let reqid = ProgramAndEnvHash(codehash, envhash);

                                if let Some(result) = computed.get(reqid) {
                                    new_runmap.insert(HashesAndPath(codehash, envhash, path), result);
                                    copy_to_runmap(&mut runmap, &new_runmap);
                                    continue;
                                }

                                if requested.contains(reqid) {
                                    copy_to_runmap(&mut runmap, &new_runmap);
                                    continue;
                                }

                                requested.insert(reqid);
                                readable.forward(readable.get_self(), RunRequest {
                                    code: constant_inputs[1],
                                    env: constant_inputs[2],
                                    replyto: readable.get_self(),
                                    treehash: sha256tree(constant_inputs[1]),
                                    envhash: sha256tree(constant_inputs[2])
                                });
                            },
                            3 =>.{
                                // Condition
                                let new_value =
                                    if truthy(constant_inputs[1]) {
                                        constant_inputs[2]
                                    } else {
                                        constant_inputs[3]
                                    };
                                new_runmap.insert(HashesAndPath(codehash, envhash, path), new_value);
                            },
                            4 => {
                                // Cons
                                new_runmap.insert(HashesAndPath(codehash, envhash, path), Constant(Rc::new(SExp::Cons(constant_inputs[1].loc(), constant_inputs[2], constant_inputs[3]))));
                            },
                            5 => {
                                // First
                                if let SExp::Cons(_,a,_) = constant_inputs[1] {
                                    new_runmap.insert(HashesAndPath(codehash, envhash, path), Constant(a.clone()));
                                } else {
                                    new_runmap.insert(HashesAndPath(codehash, envhash, path), Exception(constant_inputs[1]));
                                }
                            },
                            6 => {
                                // Rest
                                if let SExp::Cons(_,_,b) = constant_inputs[1] {
                                    new_runmap.insert(HashesAndPath(codehash, envhash, path), Constant(b.clone()));
                                } else {
                                    new_runmap.insert(HashesAndPath(codehash, envhash, path), Exception(constant_inputs[1]));
                                }
                            },
                            7 => {
                                // isList
                                let result =
                                    if let SExp::Cons(l,_,_) = constant_inputs[1] {
                                        Rc::new(SExp::Atom(l.clone(), vec![1]))
                                    } else {
                                        Rc::new(SExp::Nil(l.clone()))
                                    };
                                new_runmap.insert(HashesAndPath(codehash, envhash, path), Constant(result));
                            },
                            8 => {
                                // Exn
                                new_runmap.insert(HashesAndPath(codehash, envhash, vec![1]), Exception(make_exn_tail_list(constant_inputs)));
                            },
                            _ => {
                                // Unknown
                                todo!("don't know this op");
                            },
                        }
                    }
                }
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
