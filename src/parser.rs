use ::items::*;
use ::errors::*;

use self::ErrorKind::*;

use ::std::iter::Enumerate;
use ::std::str::Lines;

pub struct DimacsParser<'a> {
	lines: Enumerate<Lines<'a>>,
	line : usize
}

impl<'a> DimacsParser<'a> {
	#[inline]
	pub fn from_str(input: &'a str) -> DimacsParser<'a> {
		DimacsParser{
			lines: input.lines().enumerate(),
			line : 0
		}
	}

	fn mk_err(&self, kind: ErrorKind) -> DimacsError {
		DimacsError::new(self.line, kind)
	}

	#[inline]
	pub(super)
	fn err(&self, kind: ErrorKind) -> Result<DimacsItem> {
		Err(self.mk_err(kind))
	}

	fn parse_comment(&mut self, content: &str) -> Result<DimacsItem> {
		match content.find(char::is_whitespace) {
			Some(pos) => {
				let (head, tail) = content.split_at(pos);
				if head != "c" {
					debug_assert!(false); // this should never happen!
					self.err(InvalidStartOfLine)
				}
				else {
					Ok(DimacsItem::Comment(Comment::from_str(&tail[1..])))
				}
			},
			None => {
				Ok(DimacsItem::Comment(Comment::from_str("")))
			}
		}
	}

	fn expect<I: Iterator<Item=&'a str>>(&mut self, expected: &str, args: &mut I) -> Result<()> {
		match args.next() {
			Some(arg) => match arg == expected {
				true  => Ok(()),
				false => Err(self.mk_err(UnexpectedToken))
			},
			None => Err(self.mk_err(UnexpectedEndOfLine))
		}
	}

	fn parse_i64<I: Iterator<Item=&'a str>>(&mut self, args: &mut I) -> Result<i64> {
		match args.next() {
			Some(arg) => {
				arg.parse::<i64>().map_err(|_| self.mk_err(InvalidInteger))
			},
			None      => Err(self.mk_err(UnexpectedEndOfLine))
		}
	}

	fn parse_u64<I: Iterator<Item=&'a str>>(&mut self, args: &mut I) -> Result<u64> {
		let v = self.parse_i64(args)?;
		match v.is_negative() {
			true => Err(self.mk_err(UnexpectedNegativeInteger)),
			_    => Ok(v as u64)
		}
	}

	fn parse_config<I: Iterator<Item=&'a str>>(&mut self, mut args: I) -> Result<DimacsItem> {
		self.expect("p", &mut args)?;
		self.expect("cnf", &mut args)?;

		let nv = self.parse_u64(&mut args).map_err(|e|
			if e == self.mk_err(InvalidInteger) { self.mk_err(InvalidConfigNumVars) } else {e} )?;
		let nc = self.parse_u64(&mut args).map_err(|e|
			if e == self.mk_err(InvalidInteger) { self.mk_err(InvalidConfigNumClauses) } else {e} )?;

		if let Some(_) = args.next() {
			self.err(TooManyArgsForConfig)
		}
		else {
			Ok(DimacsItem::Config(Config::new(nv, nc)))
		}
	}

	fn parse_clause<I: Iterator<Item=&'a str>>(&mut self, mut args: I) -> Result<DimacsItem> {
		let mut lits = Vec::new();
		loop {
			match self.parse_i64(&mut args) {
				Ok(val) => lits.push(Lit::from_i64(val)),
				Err(e)  => match e.kind {
					UnexpectedEndOfLine => break,
					kind                => return self.err(kind)
				}
			}
		}
		match lits.pop() {
			Some(last) =>
				match last == Lit::from_i64(0) {
					true => Ok(DimacsItem::Clause(Clause::from_vec(lits))),
					_    => self.err(MissingZeroLiteralAtEndOfClause)
				},
			None => self.err(TooFewArgsForClause)
		}
	}

	fn parse_line(&mut self, line: usize, content: &'a str) -> Option<Result<DimacsItem>> {
		self.line = line + 1;
		match content.chars().next() {
			Some(c) => Some(
				match c {
					'c'        => self.parse_comment(content),
					'p'        => self.parse_config(content.split_whitespace()),
					'-'        |
					'1'...'9'  => self.parse_clause(content.split_whitespace()),
					_          => self.err(InvalidStartOfLine)
				}
			),
			None => self.next() // empty line!
		}
	}
}

impl<'a> Iterator for DimacsParser<'a> {
	type Item = Result<DimacsItem>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		match self.lines.next() {
			Some((line, content)) => self.parse_line(line, content.trim_left()),
			None                  => None
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn mk_comment(content: &str) -> Result<DimacsItem> {
		Ok(DimacsItem::Comment(Comment::from_str(content)))
	}

	fn mk_config(num_vars: u64, num_clauses: u64) -> Result<DimacsItem> {
		Ok(DimacsItem::Config(Config::new(num_vars, num_clauses)))
	}

	fn mk_clause(lits: &[i64]) -> Result<DimacsItem> {
		Ok(DimacsItem::Clause(
			Clause::from_vec(
				lits.into_iter().map(|&val| Lit::from_i64(val)).collect())))
	}

	fn mk_error(line: usize, kind: ErrorKind) -> Result<DimacsItem> {
		Err(DimacsError::new(line, kind))
	}

	fn assert_items(content: &str, expected_items: &[Result<DimacsItem>]) {
		let mut parsed_items = DimacsParser::from_str(content);
		for item in expected_items {
			assert_eq!(parsed_items.next().unwrap(), *item);
		}
		assert_eq!(parsed_items.next(), None);
	}

	#[test]
	fn valid_01() {
		assert_items(
			r"
				c This is a simplified DIMACS input file for testing purposes.
				c Such input files may start with line comments, starting with 'c'.
				c Next follows a configuration line stating the number of variables
				c and clauses used to represent this SAT instance.
				c Afterwards there is information about a clause within the SAT
				c instance for every line starting with a number and ending with '0'.
				p cnf 5 3
				 1  2  3  0
				-1  2  0
				 1 -3 -4  5  0
			",
			&[
				mk_comment("This is a simplified DIMACS input file for testing purposes."),
				mk_comment("Such input files may start with line comments, starting with 'c'."),
				mk_comment("Next follows a configuration line stating the number of variables"),
				mk_comment("and clauses used to represent this SAT instance."),
				mk_comment("Afterwards there is information about a clause within the SAT"),
				mk_comment("instance for every line starting with a number and ending with '0'."),
				mk_config(5, 3),
				mk_clause(&[ 1,  2,  3   ]),
				mk_clause(&[-1,  2       ]),
				mk_clause(&[ 1, -3, -4, 5])
			]
		)
	}

	#[test]
	fn err_multiple_configs() {
		assert_items(
			r"p cnf 5 3
			  p cnf 42 2
			",
			&[
				mk_config(5, 3),
				mk_error(2, MultipleConfigs)
			]
		)
	}

	#[test]
	fn err_missing_configs() {
		assert_items(
			r"c This is an entry comment
			  -1 0
			",
			&[
				mk_comment("This is an entry comment"),
				mk_error(2, MissingConfig),
			]
		)
	}

	#[test]
	fn err_invalid_start_of_line_01() {
		assert_items(
			r"foo",
			&[
				mk_error(1, InvalidStartOfLine),
			]
		)
	}

	#[test]
	fn err_invalid_start_of_line_02() {
		assert_items(
			r"c foo bar baz
			  c lirum larum lel  
			  p cnf 42 1337
			  -1	-2	-3	-4 0
			   1     2   3   4 0
			   0
			",
			&[
				mk_comment("foo bar baz"),
				mk_comment("lirum larum lel  "),
				mk_config(42, 1337),
				mk_clause(&[-1, -2, -3, -4]),
				mk_clause(&[ 1,  2,  3,  4]),
				mk_error(6, InvalidStartOfLine),
			]
		)
	}

	#[test]
	fn err_var_out_of_bounds() {
		assert_items(
			r"p cnf 5 10
			  1000 0
			",
			&[
				mk_config(5, 10),
				mk_error(2, VarOutOfBounds),
			]
		)
	}

	#[test]
	fn err_too_many_clauses() {
		assert_items(
			r"p cnf 9 3
			  -1  2  3 0
			   2 -3  4 0
			   3  4 -5 0
			   4 -5  6 0
			   5  6 -7 0
			",
			&[
				mk_config(9, 3),
				mk_clause(&[-1,  2,  3]),
				mk_clause(&[ 2, -3,  4]),
				mk_clause(&[ 3,  4, -5]),
				mk_error(5, TooManyClauses),
				mk_error(6, TooManyClauses),
			]
		)
	}

	fn read_file_to_string(path: &str) -> String {
		use std::io::prelude::*;
		use std::fs::File;

		let mut f = File::open(path).expect("bench file not found");
		let mut s = String::new();

		f.read_to_string(&mut s).expect("encountered problems writing bench file to string");
		s
	}

	fn test_file(path: &str) {
		let input = read_file_to_string(path);
		assert!(
			DimacsParser::from_str(input.as_str()).all(
				|item| {
					if let Err(error) = item {
						println!("{:?}", error);
						false
					}
					else {
						true
					}
				}
			)
		);
	}

	#[test]
	fn aim_100_1_6_no_1() {
		test_file("bench/aim-100-1_6-no-1.cnf")
	}

	#[test]
	fn aim_50_1_6_yes1_4() {
		test_file("bench/aim-50-1_6-yes1-4.cnf")
	}

	#[test]
	fn par_8_1_c() {
		test_file("bench/par-8-1-c.cnf")
	}

	#[test]
	fn bf0432_007() {
		test_file("bench/bf0432-007.cnf")
	}

	#[test]
	fn zebra_v155_c1135() {
		test_file("bench/zebra-v155-c1135.cnf")
	}
}

#[cfg(all(feature = "bench", test))]
mod benches {
	use super::*;

	use test::{Bencher, black_box};

	fn read_file_to_string(path: &str) -> String {
		use std::io::prelude::*;
		use std::fs::File;

		let mut f = File::open(path).expect("bench file not found");
		let mut s = String::new();

		f.read_to_string(&mut s).expect("encountered problems writing bench file to string");
		s
	}

	fn bench_file(bencher: &mut Bencher, path: &str) {
		let input = read_file_to_string(path);
		bencher.iter(|| {
			let items = DimacsParser::from_str(input.as_str()).collect::<Vec<_>>();
			black_box(items);
		});
	}

	#[bench]
	fn aim_100_1_6_no_1(bencher: &mut Bencher) {
		bench_file(bencher, "bench/aim-100-1_6-no-1.cnf")
	}

	#[bench]
	fn aim_100_1_6_yes_1_4(bencher: &mut Bencher) {
		bench_file(bencher, "bench/aim-50-1_6-yes1-4.cnf")
	}

	#[bench]
	fn bf0432_007(bencher: &mut Bencher) {
		bench_file(bencher, "bench/bf0432-007.cnf")
	}

	#[bench]
	fn zebra_v155_c1135(bencher: &mut Bencher) {
		bench_file(bencher, "bench/zebra-v155-c1135.cnf")
	}

	#[bench]
	fn par_8_1_c(bencher: &mut Bencher) {
		bench_file(bencher, "bench/par-8-1-c.cnf")
	}
}
