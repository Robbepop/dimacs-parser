//! The parser facility for parsing `.cnf` and `.sat` files as specified in the 
//! [DIMACS format specification](http://www.domagoj-babic.com/uploads/ResearchProjects/Spear/dimacs-cnf.pdf).
//! 
//! The DIMACS format was specified for the DIMACS SAT solver competitions as input file format.
//! Many other DIMACS file formats exist for other competitions, however, this crate currently only
//! supports the formats that are relevant for SAT solvers.
//! 
//! In `.cnf` the entire SAT formula is encoded as a conjunction of disjunctions and so mainly stores
//! a list of clauses consisting of literals.
//! 
//! The `.sat` format is slightly more difficult as the formula can be of a different shape and thus
//! a `.sat` file internally looks similar to a Lisp file.

#![cfg_attr(all(feature = "bench", test), feature(test))]

#![deny(missing_docs)]

#[cfg(all(feature = "bench", test))]
extern crate test;

#[macro_use]
extern crate bitflags;

mod items;
mod errors;
mod lexer;
mod parser;

pub use items::{
	Clause,
	Extensions,
	Lit,
	Var,

	Formula,
	Instance,
	Sign,

	FormulaBox,
	FormulaList
};
pub use errors::{
	Loc,
	ParseError,
	ErrorKind,
	Result
};
pub use parser::parse_dimacs;
