#[macro_use]
extern crate lazy_static;

#[macro_use]
#[cfg(all(not(test), not(target_family = "wasm"), feature = "extension-module"))]
extern crate pyo3;

extern crate tempfile;

// Python impl
#[cfg(all(not(test), not(target_family = "wasm"), feature = "extension-module"))]
mod py;
