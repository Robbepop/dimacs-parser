#![cfg_attr(all(feature = "bench", test), feature(test))]

#[cfg(all(feature = "bench", test))]
extern crate test;

extern crate itertools;

pub mod items;
pub mod errors;
pub mod functional;
pub mod imperative;
