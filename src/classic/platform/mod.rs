use std::path::PathBuf;

use crate::classic::platform::argparse::{
    ArgumentValueConv,
    ArgumentValue
};

pub mod argparse;
pub mod distutils;

pub struct PathJoin {
}

impl ArgumentValueConv for PathJoin {
    fn convert(&self, arg: &String) -> Result<ArgumentValue,String> {
        let mut p = PathBuf::new();
        p.push(arg);
        return Ok(ArgumentValue::ArgString(None, p.as_path().to_str().unwrap().to_string()));
    }
}