use clvm_tools_rs::compiler::sexp::SExp;
use clvm_tools_rs::compiler::fuzzer::FuzzProgram;
use rand::random;
use std::env;

fn main() {
    // Sickos: hahaha YES
    let prog: FuzzProgram = random();
    let args: SExp = prog.random_args();
    println!("{}", prog.to_sexp().to_string());
    println!("{}", args.to_string());
}
