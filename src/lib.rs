#![cfg_attr(all(feature = "bench", test), feature(test))]

// #![deny(missing_docs)]

#[cfg(all(feature = "bench", test))]
extern crate test;

#[macro_use]
extern crate bitflags;

pub mod items;
pub mod errors;
mod lexer;
pub mod parser;
