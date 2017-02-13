use ::std::cell::Cell;

#[derive(Debug, PartialEq, Eq)]
pub struct Var(u64);

#[derive(Debug, PartialEq, Eq)]
pub enum Sign { Pos, Neg }

#[derive(Debug, PartialEq, Eq)]
pub struct Lit(Sign, Var);

#[derive(Eq)]
pub enum DimacsItem {
	Comment(String),
	Config{num_vars: u64, num_clauses: u64},
	Clause(Box<[Lit]>),
}

impl DimacsItem {
	pub fn is_comment(&self) -> bool {
		use self::DimacsItem::*;
		match self {
			&Comment(_) => true,
			_           => false
		}
	}

	pub fn is_config(&self) -> bool {
		use self::DimacsItem::*;
		match self {
			&Config{..} => true,
			_           => false
		}
	}

	pub fn is_clause(&self) -> bool {
		use self::DimacsItem::*;
		match self {
			&Clause(_)  => true,
			_           => false
		}
	}
}

use std::fmt;
impl fmt::Debug for DimacsItem {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::DimacsItem::*;
		match self {
			&Comment(ref s) =>
				f.debug_tuple("DimacsItem::Comment")
					.field(&s)
					.finish(),
			&Config{num_vars: nv, num_clauses: nc} => 
				f.debug_struct("DimacsItem::Config")
					.field("num_vars", &nv)
					.field("num_clauses", &nc)
					.finish(),
			&Clause(ref lits) => {
				let mut tup = f.debug_tuple("DimacsItem::Clause");
				for lit in lits.iter() {
					tup.field(&lit);
				}
				tup.finish()
			}
		}
	}
}

impl PartialEq for DimacsItem {
	fn eq(&self, other: &DimacsItem) -> bool {
		use self::DimacsItem::*;
		match (self, other) {
			(&Comment(ref s1), &Comment(ref s2)) => {
				s1 == s2
			},
			(&Config{num_vars: nv1, num_clauses: nc1},
			 &Config{num_vars: nv2, num_clauses: nc2}) => {
				nv1 == nv2 && nc1 == nc2
			},
			(&Clause(ref lits1), &Clause(ref lits2)) => {
				lits1
					.iter()
					.zip(lits2.iter())
					.all(|(l1, l2)| *l1 == *l2)
			},
			_ => false
		}
	}
}

#[derive(Debug, PartialEq, Eq)]
pub enum ErrorKind {
	/// raised when the parser scans a known but unexpected token (e.g. --5)
	/// params: all expected tokens
	UnexpectedToken(Box<[String]>),

	/// raised when the parser scans an invalid token at the start of a new line
	/// this is superseeded by UnexpectedToken but its existence cleans up a lot of code.
	/// params: the scanned token
	InvalidStartOfLine(char),

	/// raised when there is a literal associated to a variable with
	/// an ID higher than the stated amount in the config
	/// params: the literal that is out of bounds and the total
	///         amount of literals specified by the config.
	VarOutOfBounds(Var, u64),

	/// raised when there are more clauses than stated in the config
	/// params: the maximum number of clauses specified by the config
	TooManyClauses(u64),

	/// raised when there are opposite literals within the same clause (e.g. a -a)
	/// param: both conflicting literals
	SelfContradictingClause(Lit, Lit), // TODO: add check

	/// raised when the parser finds no config line before the first clause line
	MissingConfig,

	/// raised when the parser finds a config after it has seen one already
	/// param: the line where the first config was found
	MultipleConfigs(usize)
}
use self::ErrorKind::*;

impl ErrorKind {
	pub fn info(&self) -> String {
		match self {
			&UnexpectedToken(ref expected) => {
				assert!(expected.len() >= 1);
				let mut expected_iter = expected.iter();
				let mut info = format!("found an unexpected token, expected: {}", expected_iter.next().unwrap());
				for tok in expected_iter {
					info.push_str(", ");
					info.push_str(tok);
				}
				info
			},
			&InvalidStartOfLine(ref found)
				=> format!(
					"found invalid character (= '{}') at the start of line.
					 valid line start characters are 'c', 'p', '-' and '1'..'9'", found),
			&VarOutOfBounds(ref var, ref bounds)
				=> format!(
					"variable {:?} is not within the specified bounds (= {}) of the config", var, bounds),
			&TooManyClauses(ref bounds)
				=> format!(
					"found more clauses than specified by the previous config (= {})", bounds),
			&SelfContradictingClause(ref lit1, ref lit2)
				=> format!(
					"found a self-contradicting clause with literals {:?} and {:?}", lit1, lit2),
			&MissingConfig
				=> format!(
					"missing a config before parsing the first clause"),
			&MultipleConfigs(line)
				=> format!(
					"found multiple configs, first at line {}", line),
		}
	}
}

#[derive(Debug, PartialEq, Eq)]
pub struct DimacsError {
	pub line  : usize,
	pub err_ch: char,
	pub kind  : ErrorKind,
	pub info  : Option<String>
}

impl DimacsError {
	pub fn new(line: usize, err_ch: char, kind: ErrorKind) -> Self {
		Self { line: line, err_ch: err_ch, kind: kind, info: None }
	}

	pub fn with_info<T: Into<String>>(line: usize, err_ch: char, kind: ErrorKind, info: T) -> Self {
		Self {
			line: line,
			err_ch: err_ch,
			kind: kind,
			info: Some(info.into())
		}
	}
}

impl fmt::Display for DimacsError {
	fn fmt(&self, f: &mut fmt::Formatter) -> ::std::fmt::Result {
		write!(f, "DimacsError::{:?} at '{}' in line {}: '{}'",
			self.kind,
			self.err_ch,
			self.line,
			self.info.clone().unwrap_or(self.kind.info())
		)
	}
}

type Result<T> = ::std::result::Result<T, DimacsError>;


/// DIMACS config with num vars and num clauses.
struct Config(u64, u64);

pub struct DimacsItemsIter<I>
	where I: Iterator<Item=char>
{
	/// the source of input
	input: I,

	/// states if the input is exhausted -> then this iterator will only yield None
	exhausted: bool,

	/// states if there was a fatal error -> then this iterator will only yield None
	error_occured: Cell<bool>,

	/// the current line within the input
	line : usize,

	/// the currently processed character
	ch: char,

	/// the line of the first already parsed config, if any.
	seen_config: Option<(usize, Config)>,

	/// count of parsed clauses
	clauses_parsed: u64
}

impl<I> DimacsItemsIter<I>
	where I: Iterator<Item=char>
{
	pub fn new(input: I) -> Self {
		let mut iter = Self{
			input: input,
			exhausted: false,
			error_occured: Cell::new(false),
			line: 1,
			ch: '\0',
			seen_config: None,
			clauses_parsed: 0
		};
		iter.bump();
		iter
	}

	fn bump(&mut self) -> Option<char> {
		if let Some(next_ch) = self.input.next() {
			self.ch = next_ch;
			if self.ch == '\n' { self.line += 1; }
			Some(self.ch)
		}
		else {
			self.exhausted = true;
			None
		}
	}

	fn expect_ch(&mut self, expected_ch: char) -> Result<()> {
		self.expect_ch_with_info(expected_ch, format!("expected '{}'", expected_ch))
	}

	fn expect_ch_with_info<T: Into<String>>(&mut self, expected_ch: char, info: T) -> Result<()> {
		if self.ch != expected_ch {
			Err(self.error_with_info(
				UnexpectedToken(vec![format!("{}", expected_ch)].into_boxed_slice()),
				info))
		}
		else {
			self.bump();
			Ok(())
		}
	}

	fn expect_str(&mut self, expected_str: &str) -> Result<()> {
		for c in expected_str.chars() {
			self.expect_ch(c)?;
		}
		Ok(())
	}

	fn expect_any_ch(&mut self, expected: &[char]) -> Result<()> {
		if expected.iter().all(|&c| self.ch != c) {
			let boxed = expected.iter().map(|c| format!("{}", c)).collect::<Vec<String>>().into_boxed_slice();
			Err(self.error(UnexpectedToken(boxed)))
		}
		else {
			self.bump();
			Ok(())
		}
	}

	fn skip_inline_whitespace(&mut self) {
		while self.ch == '\t' || self.ch == ' ' { self.bump(); }
	}

	fn expect_whitespace(&mut self) -> Result<()> {
		self.expect_any_ch(&['\t', ' '])?;
		self.skip_inline_whitespace();
		Ok(())
	}

	fn parse_comment(&mut self) -> Result<DimacsItem> {
		debug_assert_eq!(self.ch, 'c');

		self.expect_ch('c')?;
		self.skip_inline_whitespace();

		let mut buffer = String::new();
		while self.ch != '\n' {
			buffer.push(self.ch);
			self.bump();
		}
		self.expect_ch('\n')?;

		Ok(DimacsItem::Comment(buffer))
	}

	fn parse_config(&mut self) -> Result<DimacsItem> {
		debug_assert_eq!(self.ch, 'p');

		self.expect_ch('p')?;
		self.expect_whitespace()?;
		self.expect_str("cnf")?;
		self.expect_whitespace()?;

		let num_vars    = self.parse_uint()?;
		self.expect_whitespace()?;
		let num_clauses = self.parse_uint()?;
		self.skip_inline_whitespace();
		self.expect_ch('\n')?;

		if let Some((prev_cfg_line, _)) = self.seen_config {
			Err(self.error(MultipleConfigs(prev_cfg_line)))
		}
		else {
			self.seen_config = Some((self.line, Config(num_vars, num_clauses)));
			Ok(DimacsItem::Config{num_vars: num_vars, num_clauses: num_clauses})
		}
	}

	fn is_at_start_of_uint(&self) -> bool {
		self.ch != '0' && self.ch.is_digit(10)
	}

	fn parse_uint(&mut self) -> Result<u64> {
		debug_assert!(self.is_at_start_of_uint());

		let mut val = 0u64;
		while self.ch.is_digit(10) {
			val *= 10;
			val += self.ch.to_digit(10).unwrap() as u64;
			self.bump();
		}

		Ok(val)
	}

	fn is_at_start_of_int(&self) -> bool {
		self.is_at_start_of_uint() || self.ch == '-'
	}

	fn parse_int(&mut self) -> Result<i64> {
		debug_assert!(self.is_at_start_of_int());

		let signum: i64 = if self.ch == '-' { self.bump(); -1 } else { 1 };
		let val   : i64 = self.parse_uint()? as i64;

		Ok(signum * val)
	}

	fn is_at_start_of_lit(&self) -> bool {
		self.is_at_start_of_int()
	}

	fn parse_lit(&mut self) -> Result<Lit> {
		debug_assert!(self.is_at_start_of_lit());
		let val  = self.parse_int()?;
		let sign = if val >= 0 { Sign::Pos } else { Sign::Neg };
		let abs  = val.abs() as u64;
		if let Some((_, Config(num_vars, _))) = self.seen_config {
			if abs <= num_vars {
				Ok(Lit(sign, Var(abs)))
			}
			else {
				Err(self.error(VarOutOfBounds(Var(abs), num_vars)))
			}
		}
		else {
			Err(self.error(MissingConfig))
		}
	}

	fn parse_clause(&mut self) -> Result<DimacsItem> {
		debug_assert!(self.is_at_start_of_lit());

		if let Some((_, Config(_, num_clauses))) = self.seen_config {
			let mut lits = Vec::new();
			while self.is_at_start_of_lit() {
				lits.push(self.parse_lit()?);
				self.expect_whitespace()?;
			}

			self.expect_ch('0')?;
			self.expect_ch('\n')?;

			self.clauses_parsed += 1;
			if self.clauses_parsed > num_clauses {
				Err(self.error(TooManyClauses(num_clauses)))
			}
			else {
				Ok(DimacsItem::Clause(lits.into_boxed_slice()))
			}
		}
		else {
			Err(self.error(MissingConfig))
		}
	}

	fn error(&self, kind: ErrorKind) -> DimacsError {
		self.error_occured.set(true);
		DimacsError::new(self.line, self.ch, kind)
	}

	fn error_with_info<T: Into<String>>(&self, kind: ErrorKind, info: T) -> DimacsError {
		self.error_occured.set(true);
		DimacsError::with_info(self.line, self.ch, kind, info)
	}
}

impl<I> Iterator for DimacsItemsIter<I>
	where I: Iterator<Item=char>
{
	type Item = Result<DimacsItem>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.exhausted || self.error_occured.get() {
			None
		}
		else {
			match self.ch {
				'c'       => Some(self.parse_comment()),
				'p'       => Some(self.parse_config()),
				'-'       |
				'1'...'9' => Some(self.parse_clause()),
				'\r'|'\n'|'\t'|' ' => { self.bump(); self.next() },
				_         => Some(Err(self.error(InvalidStartOfLine(self.ch))))
			}
		}
	}
}

pub trait DimacsIter<I>
	where I: Iterator<Item=char>
{
	fn dimacs_items(self) -> DimacsItemsIter<I>;
}

impl<I> DimacsIter<I> for I
	where I: Iterator<Item=char>
{
	fn dimacs_items(self) -> DimacsItemsIter<I> {
		DimacsItemsIter::new(self)
	}
}

pub struct Clause(Box<[Lit]>);

pub struct Instance {
	num_vars: u64,
	clauses : Box<[Clause]>
}

impl Instance {
	pub fn new(num_vars: u64, clauses: Box<[Clause]>) -> Self {
		Self{
			num_vars: num_vars,
			clauses: clauses
		}
	}

	pub fn num_vars(&self) -> u64 {
		self.num_vars
	}

	pub fn num_clauses(&self) -> u64 {
		self.clauses.len() as u64
	}

	pub fn clauses(&self) -> &[Clause] {
		&self.clauses[..]
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn mk_comment(content: &str) -> Result<DimacsItem> {
		Ok(DimacsItem::Comment(String::from(content)))
	}

	fn mk_config(num_vars: u64, num_clauses: u64) -> Result<DimacsItem> {
		Ok(DimacsItem::Config{num_vars: num_vars, num_clauses: num_clauses})
	}

	fn mk_clause(lits: &[i64]) -> Result<DimacsItem> {
		Ok(
			DimacsItem::Clause(
				lits
					.into_iter()
					.map(|&x| (x >= 0, x.abs()))
					.map(|(pos, val)| Lit(if pos { Sign::Pos } else { Sign::Neg }, Var(val as u64)))
					.collect::<Vec<_>>().into_boxed_slice())
		)
	}

	fn mk_error(line: usize, ch: char, kind: ErrorKind) -> Result<DimacsItem> {
		Err(DimacsError::new(line, ch, kind))
	}

	fn assert_items(content: &str, items: &[Result<DimacsItem>]) {
		let mut dimacs_iter = content.chars().dimacs_items();
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
				mk_error(3, '\t', MultipleConfigs(2))
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
				mk_error(2, '-', MissingConfig),
			]
		)
	}

	#[test]
	fn err_invalid_start_of_line_01() {
		assert_items(
			r"foo",
			&[
				mk_error(1, 'f', InvalidStartOfLine('f')),
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
				mk_error(6, '0', InvalidStartOfLine('0')),
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
				mk_error(2, ' ', VarOutOfBounds(Var(1000), 5)),
			]
		)
	}

	#[test]
	fn err_clauses_out_of_bounds() {
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
				mk_error(6, '\t', TooManyClauses(3)),
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
		assert!(input.chars().dimacs_items().all(|item| item.is_ok()));
	}

	#[test]
	fn aim_100_1_6_no_1() {
		test_file("bench/aim-100-1_6-no-1.cnf")
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
			let items = input.chars().dimacs_items().collect::<Vec<_>>();
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
