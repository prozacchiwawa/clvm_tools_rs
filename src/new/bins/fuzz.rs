use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use clvm_tools_rs::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

use clvm_tools_rs::compiler::prims;
use clvm_tools_rs::compiler::srcloc::Srcloc;
use clvm_tools_rs::compiler::clvm::run;
use clvm_tools_rs::compiler::compiler::{ DefaultCompilerOpts, compile_file };

use clvm_tools_rs::compiler::sexp::SExp;
use clvm_tools_rs::compiler::fuzzer::{FuzzProgram, rng_from_string};
use clvm_tools_rs::compiler::runtypes::RunFailure;

use rand::Rng;
use rand::SeedableRng;
use rand::rngs::SmallRng;
use std::env;

fn main() {
    let mut allocator = Allocator::new();
    let opts = Rc::new(DefaultCompilerOpts::new(&"*prog*".to_string()));
    let runner = Rc::new(DefaultProgramRunner::new());
    let prim_map = prims::prim_map();

    let mut random_seed =
        env::var("RANDOM_SEED").unwrap_or_else(|_| {
            let mut protogen = SmallRng::from_entropy();
            let random_atom = SExp::random_atom(&mut protogen);
            random_atom.to_string()
        });

    // Sickos: hahaha YES
    let mut rng = rng_from_string(random_seed.clone());
    let prog: FuzzProgram = rng.gen();

    println!("random-seed: {}", random_seed);
    println!("prog: {}", prog.to_sexp().to_string());

    compile_file(
        &mut allocator,
        runner.clone(),
        opts.clone(),
        &prog.to_sexp().to_string()
    ).map_err(|e| RunFailure::RunErr(e.0, e.1)).and_then(|compiled| {
        println!("compiled: {}", compiled.to_string());

        let args = prog.random_args(&mut rng);
        println!("args: {}", args.to_string());

        let interp_res = prog.interpret(Rc::new(args.clone()));
        match interp_res {
            Ok(r) => println!("interp-ok: {}", r.to_string()),
            Err(e) => println!("interp-error: {}", e.to_string())
        }

        run(
            &mut allocator,
            runner.clone(),
            prim_map,
            Rc::new(compiled),
            Rc::new(args)
        )
    }).map(|after_run| {
        println!("result: {}", after_run.to_string());
    }).unwrap_or_else(|e| panic!("error: {:?}", e))
}
