/* Implement retained symbols in modern mode
 * Since we have more info per symbol, we'll make the encoding flexible so more
 * could be added.  The end result will be a dump of the loc() member from each
 * element of the output by path, since it's something we have after compilation
 * and can reattach after reading.
 */
use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::{BigInt, ToBigInt};

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

#[derive(Clone, Debug)]
pub enum SymbolKind {
    Kind21(Srcloc)
}

impl SymbolKind {
    pub fn to_symstore(&self) -> String {
        match self {
            SymbolKind::Kind21(l) => format!("t21:{}", l.to_string())
        }
    }
}

pub struct SymbolStore {
    symbols: HashMap<BigInt, SymbolKind>
}

fn collect_with_path(symstore: &mut SymbolStore, sexp: Rc<SExp>, path: BigInt, next_bit: BigInt) {
    let next_level_bit = next_bit.clone() * 2u32.to_bigint().unwrap();
    match sexp.borrow() {
        SExp::Cons(l,a,b) => {
            symstore.add(path.clone() | next_bit.clone(), SymbolKind::Kind21(l.clone()));
            let (left_path, right_path) =
                (path.clone(), path.clone() | next_bit.clone());

            collect_with_path(symstore, a.clone(), left_path, next_level_bit.clone());
            collect_with_path(symstore, b.clone(), right_path, next_level_bit);
        },
        _ => {
            symstore.add(path.clone() | next_bit.clone(), SymbolKind::Kind21(sexp.loc()))
        }
    }
}

fn apply_symbols(symstore: &SymbolStore, sexp: Rc<SExp>, path: BigInt, next_bit: BigInt) -> Rc<SExp> {
    let next_level_bit = next_bit.clone() * 2u32.to_bigint().unwrap();
    let new_loc =
        symstore.lookup(path.clone() | next_bit.clone()).map(|l| {
            match l {
                SymbolKind::Kind21(l) => l.clone()
            }
        }).unwrap_or_else(|| sexp.loc());

    match sexp.borrow() {
        SExp::Cons(l,a,b) => {
            Rc::new(SExp::Cons(
                new_loc,
                apply_symbols(symstore, a.clone(), path.clone(), next_level_bit.clone()),
                apply_symbols(symstore, b.clone(), path.clone() | next_bit.clone(), next_level_bit.clone()),
            ))
        },
        _ => Rc::new(sexp.with_loc(new_loc))
    }
}

impl SymbolStore {
    pub fn lookup(&self, path: BigInt) -> Option<SymbolKind> {
        self.symbols.get(&path).map(|x| x.clone())
    }

    pub fn apply(&self, sexp: Rc<SExp>) -> Rc<SExp> {
        apply_symbols(
            self,
            sexp,
            0u32.to_bigint().unwrap(),
            1u32.to_bigint().unwrap()
        )
    }

    pub fn add(&mut self, path: BigInt, data: SymbolKind) {
        self.symbols.insert(path, data);
    }

    pub fn collect(sexp: Rc<SExp>) -> SymbolStore {
        let mut symstore = SymbolStore {
            symbols: HashMap::new()
        };
        collect_with_path(
            &mut symstore,
            sexp,
            1u32.to_bigint().unwrap(),
            1u32.to_bigint().unwrap()
        );

        symstore
    }

    pub fn to_stringmap(&self) -> HashMap<String, String> {
        let mut res = HashMap::new();

        for (name, val) in self.symbols.iter() {
            res.insert(format!("path:{}", name.to_string()), val.to_symstore());
        }

        res
    }

    pub fn from_stringmap(h: &HashMap<String, String>) -> Option<SymbolStore> {
        let mut fnames = HashMap::new();
        let mut ss = SymbolStore {
            symbols: HashMap::new()
        };

        for (name, val) in h.iter() {
            match name.get(..5).and_then(|n| {
                if n == "path" {
                    n.get(5..).and_then(|bi| {
                        BigInt::parse_bytes(bi.as_bytes(), 10)
                    })
                } else {
                    None
                }
            }).and_then(|path| {
                val.get(..4).map(|v| (path, v))
            }).and_then(|(path, v)| {
                if v == "t21:" {
                    val.get(4..)
                        .and_then(|sl| Srcloc::parse(&mut fnames, &sl.to_string()))
                        .map(|loc| (path, loc))
                } else {
                    None
                }
            }) {
                Some((path,loc)) => { ss.add(path, SymbolKind::Kind21(loc)); }
                _ => { }
            }
        }

        if ss.symbols.is_empty() {
            None
        } else {
            Some(ss)
        }
    }
}
