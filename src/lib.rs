#![cfg_attr(all(feature = "bench", test), feature(test))]

#[cfg(all(feature = "bench", test))]
extern crate test;

#[macro_use]
extern crate bitflags;

extern crate itertools;
extern crate fnv;
extern crate unreachable;

pub mod items;
pub mod errors;
pub mod lexer;
pub mod parser;
