#![feature(pub_restricted)]
// #![feature(slice_patterns)]

#![cfg_attr(all(feature = "bench", test), feature(test))]

#[cfg(all(feature = "bench", test))]
extern crate test;

extern crate itertools;
extern crate fnv;
extern crate unreachable;

pub mod items;
pub mod errors;
pub mod lexer;
// pub mod parser;
