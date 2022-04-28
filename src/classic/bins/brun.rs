use clvm_tools_rlib::classic::clvm_tools::cmds::brun;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    brun(&args);
}
