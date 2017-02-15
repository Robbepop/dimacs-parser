use ::items::*;
use ::errors::*;
use ::parser::*;

use ::std::collections::HashSet;

use self::ErrorKind::*;

pub struct EnhancedDimacsParser<'a> {
	parser: DimacsParser<'a>,
	seen_config: Option<Config>,
	parsed_clauses: usize,
	used_lits: HashSet<Lit>
}

impl<'a> EnhancedDimacsParser<'a> {
	pub fn from_str(input: &str) -> EnhancedDimacsParser {
		EnhancedDimacsParser{
			parser: DimacsParser::from_str(input),
			seen_config: None,
			parsed_clauses: 0,
			used_lits: HashSet::new()
		}
	}

	fn check_config(&mut self, config: Config) -> Result<DimacsItem> {
		match self.seen_config {
			Some(_) => self.parser.err(MultipleConfigs),
			None    => {
				self.seen_config = Some(config);
				Ok(DimacsItem::Config(config))
			}
		}
	}

	fn check_clause(&mut self, clause: Clause) -> Result<DimacsItem> {
		match self.seen_config {
			None      => self.parser.err(MissingConfig),
			Some(cfg) => {
				self.parsed_clauses += 1;
				match self.parsed_clauses as u64 <= cfg.num_clauses() {
					true  => {
						for &lit in clause.lits() {
							if lit.var().0 > cfg.num_vars() {
								return self.parser.err(VarOutOfBounds)
							}
							self.used_lits.insert(lit);
						}
						Ok(DimacsItem::Clause(clause))
					},
					false => self.parser.err(TooManyClauses)
				}
			}
		}
	}

	fn check_item(&mut self, item: DimacsItem) -> Result<DimacsItem> {
		match item {
			DimacsItem::Comment(comment) => Ok(DimacsItem::Comment(comment)),
			DimacsItem::Config(config)   => self.check_config(config),
			DimacsItem::Clause(clause)   => self.check_clause(clause)
		}
	}

	fn forward_or_check(&mut self, res_item: Result<DimacsItem>) -> Result<DimacsItem> {
		match res_item {
			Ok(item) => self.check_item(item),
			Err(e)   => Err(e)
		}
	}
}

impl<'a> Iterator for EnhancedDimacsParser<'a> {
	type Item = Result<DimacsItem>;

	fn next(&mut self) -> Option<Self::Item> {
		match self.parser.next() {
			Some(item) => Some(self.forward_or_check(item)),
			None => None
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
		let mut parsed_items = EnhancedDimacsParser::from_str(content);
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
			EnhancedDimacsParser::from_str(input.as_str()).all(
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
			let items = EnhancedDimacsParser::from_str(input.as_str()).collect::<Vec<_>>();
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
