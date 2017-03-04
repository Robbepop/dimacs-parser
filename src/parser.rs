use lexer::*;
use errors::*;
use items::*;

#[derive(Debug, Clone)]
pub struct Parser<I>
	where I: Iterator<Item=char>
{
	input: ValidLexer<I>
}

impl<I> Parser<I>
	where I: Iterator<Item=char>
{
	pub fn from(input: I) -> Parser<I> {
		Parser{
			input: ValidLexer::from(input)
		}
	}

	fn parse_header(&mut self) -> Result<Problem> {
		Ok(Problem::cnf(0, 0)) // TODO!
	}

	fn parse_clauses(&mut self, num_clauses: u64) -> Result<Vec<Clause>> {
		let clauses: Vec<Clause> = Vec::with_capacity(num_clauses as usize);
		Ok(clauses) // TODO!
	}

	fn parse_cnf(&mut self, num_vars: u64, num_clauses: u64) -> Result<Instance> {
		Ok(Instance::cnf(num_vars, self.parse_clauses(num_clauses)?))
	}

	fn parse_formula(&mut self) -> Result<Formula> {
		Ok(Formula::Lit(Lit::from_i64(0))) // TODO!
	}

	fn parse_sat(&mut self, num_vars: u64, extensions: Box<[Extension]>) -> Result<Instance> {
		Ok(Instance::sat_with_ext(num_vars, extensions.to_vec(), self.parse_formula()?))
	}

	pub fn parse_dimacs(&mut self) -> Result<Instance> {
		match self.parse_header()? {
			Problem::Cnf{num_vars, num_clauses} => self.parse_cnf(num_vars, num_clauses),
			Problem::Sat{num_vars, extensions } => self.parse_sat(num_vars, extensions)
		}
	}
}

pub fn parse_dimacs(input: &str) -> Result<Instance> {
	Parser::from(input.chars()).parse_dimacs()
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn simple_cnf() {
		let sample = r"
			c Sample DIMACS .cnf file
			c holding some information
			c and trying to be some
			c kind of a test.
			p cnf 42 1337
			1 2 0
			-3 4 0
			5 -6 7 0
			-7 -8 -9 0";
		let parsed = parse_dimacs(sample).expect("valid .cnf");
		let expected = Instance::cnf(42, vec![
			Clause::from_vec(vec![Lit::from_i64( 1), Lit::from_i64( 2)]),
			Clause::from_vec(vec![Lit::from_i64(-3), Lit::from_i64( 4)]),
			Clause::from_vec(vec![Lit::from_i64( 5), Lit::from_i64(-6), Lit::from_i64( 7)]),
			Clause::from_vec(vec![Lit::from_i64(-7), Lit::from_i64(-8), Lit::from_i64(-9)])
		]);
		assert_eq!(parsed, expected);
	}

	#[test]
	fn simple_sat() {
		let sample = r"
			c Sample DIMACS .sat file
			p sat 42
			(*(+(1 3 -4)
			+(4)
			+(2 3)))";
		let parsed = parse_dimacs(sample).expect("valid .sat");
		let expected = Instance::sat(42,
			Formula::paren(
				Formula::and(vec![
					Formula::or(vec![
						Formula::lit(Lit::from_i64(1)), Formula::lit(Lit::from_i64(3)), Formula::lit(Lit::from_i64(-4))
					]),
					Formula::or(vec![
						Formula::lit(Lit::from_i64(4))
					]),
					Formula::or(vec![
						Formula::lit(Lit::from_i64(2)), Formula::lit(Lit::from_i64(3))
					])
				])
			)
		);
		assert_eq!(parsed, expected);
	}
}
