use ::items::*;
use ::errors::*;

use self::ErrorKind::*;

fn is_start_of_clause(head: &str) -> bool {
	if let Some(ch) = head.chars().next() {
		match ch {
			'c' | 'p' | '-' | '1'...'9' => true,
			_                           => false
		}
	}
	else {
		false
	}
}

fn parse_comment<'a, I: Iterator<Item=&'a str>>(line: usize, mut args: I) -> Result<DimacsItem> {
	expect_str("c", args.next(), line)?;
	use itertools::*;
	Ok(
		DimacsItem::Comment(Comment::from_string(args.join(" ")))
	)
}

fn expect_str<'a>(expected: &str, input: Option<&str>, line: usize) -> Result<()> {
	match input {
		Some(content) => {
			match content == expected {
				true => Ok(()),
				_    => Err(DimacsError::new(line, UnexpectedToken))
			}
		},
		None => Err(DimacsError::new(line, UnexpectedEndOfLine))
	}
}

fn parse_config<'a, I: Iterator<Item=&'a str>>(line: usize, mut args: I) -> Result<DimacsItem> {
	expect_str("p"  , args.next(), line)?;
	expect_str("cnf", args.next(), line)?;

	let nv =
		match args.next() {
			Some(arg_nv) =>
				match arg_nv.parse::<u64>() {
					Ok(nv) => Ok(nv),
					_      => Err(DimacsError::new(line, InvalidConfigNumVars))
				},
			None => Err(DimacsError::new(line, TooFewArgsForConfig))
		}?;

	let nc =
		match args.next() {
			Some(arg_nv) =>
				match arg_nv.parse::<u64>() {
					Ok(nc) => Ok(nc),
					_      => Err(DimacsError::new(line, InvalidConfigNumClauses))
				},
			None => Err(DimacsError::new(line, TooFewArgsForConfig))
		}?;

	match args.next() {
		Some(_) => Err(DimacsError::new(line, TooManyArgsForConfig)),
		None    => Ok(DimacsItem::Config(Config::new(nv, nc)))
	}
}

fn parse_lit(line: usize, arg: &str) -> Result<Lit> {
	match arg.parse::<i64>() {
		Ok(val) => Ok(Lit::from_i64(val)),
		_       => Err(DimacsError::new(line, InvalidClauseLit))
	}
}

fn parse_clause<'a, I: Iterator<Item=&'a str>>(line: usize, args: I) -> Result<DimacsItem> {
	let mut lits = Vec::new();
	for arg in args { lits.push(parse_lit(line, arg)?); }
	if lits.len() < 2 {
		Err(DimacsError::new(line, TooFewArgsForClause))
	}
	else if let Some(Var(0)) = lits.pop().map(|lit| lit.var()) {
		Ok(DimacsItem::Clause(Clause::from_vec(lits)))
	}
	else {
		Err(DimacsError::new(line, MissingZeroLiteralAtEndOfClause))
	}
}

fn parse_dimacs_item<'a, I: 'a + Iterator<Item=&'a str>>(line: usize, head: &'a str, args: I) -> Result<DimacsItem> {
	match head {
		"c" => parse_comment(line, args),
		"p" => parse_config(line, args),
		c if is_start_of_clause(c)
		    => parse_clause(line, args),
		_   => Err(DimacsError::new(line, InvalidStartOfLine))
	}
}

/// Iterator over `DimacsItem`.
/// 
/// Is missing some high-level checks for the DIMACS format and thus is a bit faster.
fn parse_dimacs<'a>(input: &'a str) -> Box< Iterator< Item=(usize, Result<DimacsItem>)> + 'a > {
	Box::new(
		input

		// iterate over all lines
		.lines()

		// split all lines at the whitespace
		.map(|content| content.split_whitespace().peekable())

		// add line counts
		.enumerate()

		// lines should start at 1 instead of 0
		.map(|(line0, content)| (line0+1, content))

		// filter empty lines and extract head
		.filter_map(|(line, mut tokens)| {
			if let Some(&head) = tokens.peek() {
				Some((line, (head, tokens)))
			}
			else {
				None
			}
		})

		// convert to line + Result<DimacsItem>
		.map(|(line, (head, args))| (line, parse_dimacs_item(line, head, args)) )
	)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct LineAndConfig(usize, Config);

impl LineAndConfig {
	fn num_vars(&self) -> u64 {
		self.1.num_vars()
	}

	fn num_clauses(&self) -> u64 {
		self.1.num_clauses()
	}
}

pub struct DimacsIter<'a> {
	parser: Box<Iterator<Item=(usize, Result<DimacsItem>)> + 'a>,
	seen_config: Option<LineAndConfig>,
	parsed_clauses: u64
}

impl<'a> DimacsIter<'a> {
	pub fn from_str(input: &'a str) -> DimacsIter {
		DimacsIter{
			parser: parse_dimacs(input),
			seen_config: None,
			parsed_clauses: 0,
		}
	}

	fn check_config(&mut self, line: usize, cfg: Config) -> Result<DimacsItem> {
		match self.seen_config {
			Some(_) => Err(DimacsError::new(line, MultipleConfigs)),
			None    => {
				self.seen_config = Some(LineAndConfig(0, cfg));
				Ok(DimacsItem::Config(cfg))
			}
		}
	}

	fn check_clause(&mut self, line: usize, item: Clause) -> Result<DimacsItem> {
		match self.seen_config {
			None         => Err(DimacsError::new(line, MissingConfig)),
			Some(config) => {
				if item.lits().iter().all(|lit| lit.var().0 <= config.num_vars()) {
					if self.parsed_clauses >= config.num_clauses() {
						Err(DimacsError::new(line, TooManyClauses))
					}
					else {
						self.parsed_clauses += 1;
						Ok(DimacsItem::Clause(item))
					}
				}
				else {
					Err(DimacsError::new(line, VarOutOfBounds))
				}
			}
		}
	}

	fn check_item(&mut self, line: usize, item: DimacsItem) -> Result<DimacsItem> {
		use self::DimacsItem::*;
		match item {
			Config(cfg)      => self.check_config(line, cfg),
			Clause(clause)   => self.check_clause(line, clause),
			Comment(comment) => Ok(Comment(comment))
		}
	}
}

impl<'a> Iterator for DimacsIter<'a> {
	type Item = Result<DimacsItem>;

	fn next(&mut self) -> Option<Self::Item> {
		match self.parser.next() {
			Some(result_item) => Some(
				match result_item {
					(line, Ok(item)) => self.check_item(line, item),
					( .. ,    err  ) => err
				}
			),
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

	fn assert_items(content: &str, items: &[Result<DimacsItem>]) {
		let mut dimacs_iter = DimacsIter::from_str(content);
		for item in items {
			assert_eq!(dimacs_iter.next().unwrap(), *item);
		}
		assert_eq!(dimacs_iter.next(), None);
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
				mk_comment("lirum larum lel"),
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
			DimacsIter::from_str(input.as_str()).all(
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
			let items = DimacsIter::from_str(input.as_str()).collect::<Vec<_>>();
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
