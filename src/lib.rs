#![feature(pub_restricted)]
// #![feature(slice_patterns)]

#![cfg_attr(all(feature = "bench", test), feature(test))]

#[cfg(all(feature = "bench", test))]
extern crate test;

extern crate itertools;

pub mod items;
pub mod errors;
pub mod parser;
pub mod enhanced_parser;
