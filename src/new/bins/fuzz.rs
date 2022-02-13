use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use clvm_tools_rs::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

use clvm_tools_rs::compiler::prims;
use clvm_tools_rs::compiler::srcloc::Srcloc;
use clvm_tools_rs::compiler::clvm::run;

use clvm_tools_rs::compiler::sexp::SExp;
use clvm_tools_rs::compiler::fuzzer::FuzzProgram;
use rand::random;
use std::env;

fn main() {
    let loc = Srcloc::start(&"*prog*".to_string());
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let prim_map = prims::prim_map();

    // Sickos: hahaha YES
    let prog: FuzzProgram = random();
    let args: SExp = prog.random_args();

    println!("prog: {}", prog.to_sexp().to_string());

    let args = prog.random_args();
    println!("args: {}", args.to_string());

    run(
        &mut allocator,
        runner.clone(),
        prim_map,
        Rc::new(prog.to_sexp()),
        Rc::new(args)
    ).map(|after_run| {
        println!("result: {}", after_run.to_string());
    }).unwrap_or_else(|e| panic!("error: {:?}", e))
}
