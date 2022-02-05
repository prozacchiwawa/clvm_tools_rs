use clvm_tools_rs::compiler::sexp::SExp;
use rand::random;
use std::env;

fn main() {
    // let args: Vec<String> = env::args().collect();
    let sexp: SExp = random();
    println!("{}", sexp.to_string());
}
