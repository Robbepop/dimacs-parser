use lexer::*;
use errors::*;
use items::*;

#[derive(Debug, Clone)]
pub struct Parser<I>
	where I: Iterator<Item=char>
{
	tokens: ValidLexer<I>,
	peek  : Result<Token>
}

impl<I> Parser<I>
	where I: Iterator<Item=char>
{
	pub fn from(input: I) -> Parser<I> {
		Parser{
			tokens: ValidLexer::from(input),
			peek  : Err(ParseError::new(Loc::new(0, 0), ErrorKind::EmptyTokenStream))
		}
	}

	fn mk_err(&self, kind: ErrorKind) -> ParseError {
		println!("Parser::mk_err");
		ParseError::new(self.peek_loc(), kind)
	}

	fn token_err(&self, kind: ErrorKind) -> Result<Token> {
		println!("Parser::token_err");
		Err(self.mk_err(kind))
	}

	fn formula_err(&self, kind: ErrorKind) -> Result<Formula> {
		println!("Parser::formula_err");
		Err(self.mk_err(kind))
	}

	fn peek_loc(&self) -> Loc {
		println!("Parser::peek_loc");
		match self.peek {
			Ok(tok)  => tok.loc(),
			Err(err) => err.loc
		}
	}

	fn consume(&mut self) -> Result<Token> {
		println!("Parser::consume");
		self.peek = self.tokens
			.next()
			.unwrap_or(Ok(Token::new(self.peek_loc(), TokenKind::EndOfFile)));
		self.peek
	}

	fn expect(&mut self, expected: TokenKind) -> Result<Token> {
		println!("Parser::expect");
		use self::TokenKind::EndOfFile;
		use self::ErrorKind::{UnexpectedEndOfFile, UnexpectedToken};
		match self.peek?.kind() {
			k if k == expected => self.consume(),
			EndOfFile          => self.token_err(UnexpectedEndOfFile),
			_                  => self.token_err(UnexpectedToken)
		}
	}

	fn expect_nat(&mut self) -> Result<u64> {
		println!("Parser::expect_nat");
		match self.peek?.kind() {
			TokenKind::Nat(val) => {
				self.consume()?;
				Ok(val)
			},
			_ => Err(self.mk_err(ErrorKind::UnexpectedToken))
		}
	}

	fn parse_header(&mut self) -> Result<Instance> {
		println!("Parser::parse_header");
		use self::TokenKind::{Ident};
		use self::Ident::*;
		self.expect(Ident(Problem))?;
		match self.peek?.kind() {
			Ident(Cnf)   => self.parse_cnf_header(),
			Ident(Sat)   |
			Ident(Sate)  |
			Ident(Satx)  |
			Ident(Satex) => self.parse_sat_header(),
			_ => Err(self.mk_err(ErrorKind::UnexpectedToken))
		}
	}

	fn parse_cnf_header(&mut self) -> Result<Instance> {
		println!("Parser::parse_cnf_header");
		self.expect(TokenKind::Ident(Ident::Cnf))?;
		let num_vars    = self.expect_nat()?;
		let num_clauses = self.expect_nat()?;
		Ok(Instance::cnf(num_vars, self.parse_clauses(num_clauses)?))
	}

	fn parse_clauses(&mut self, num_clauses: u64) -> Result<Vec<Clause>> {
		println!("Parser::parse_clauses");
		let clauses: Vec<Clause> = Vec::with_capacity(num_clauses as usize);
		Ok(clauses) // TODO!
	}

	fn parse_sat_extensions<'a>(&'a mut self) -> Result<Extensions> {
		println!("Parser::parse_sat_extensions");
		use self::TokenKind::{Ident};
		use self::Ident::{Sat, Sate, Satx, Satex};
		use self::ErrorKind::*;
		match self.peek?.kind() {
			Ident(Sat)   => { self.consume()?; Ok(NONE) },
			Ident(Sate)  => { self.consume()?; Ok(EQ) },
			Ident(Satx)  => { self.consume()?; Ok(XOR) },
			Ident(Satex) => { self.consume()?; Ok(EQ | XOR) },
			_ => Err(self.mk_err(InvalidSatExtension))
		}
	}

	fn parse_sat_header(&mut self) -> Result<Instance> {
		println!("Parser::parse_sat_header");
		let extensions = self.parse_sat_extensions()?;
		let num_vars   = self.expect_nat()?;
		Ok(Instance::sat(num_vars, extensions, self.parse_paren_formula()?))
	}

	fn parse_formula(&mut self) -> Result<Formula> {
		println!("Parser::parse_formula");
		use lexer::TokenKind::*;
		use lexer::Ident::*;
		let tok = self.peek?;
		match tok.kind() {
			Nat(val)   => { self.consume()?; Ok(Formula::lit(Lit::from_i64(val as i64))) },
			Open       => self.parse_paren_formula(),
			Plus       => self.parse_or_formula(),
			Star       => self.parse_and_formula(),
			Minus      => self.parse_neg_formula(),
			Eq         => self.parse_eq_formula(),
			Ident(Xor) => self.parse_xor_formula(),
			_          => self.formula_err(ErrorKind::UnexpectedToken)
		}
	}

	fn parse_formula_list(&mut self) -> Result<Vec<Formula>> {
		println!("Parser::parse_formula_list");
		let mut formulas = Vec::new();
		while self.peek?.kind() != TokenKind::Close {
			formulas.push(self.parse_formula()?);
		}
		Ok(formulas)
	}

	fn parse_formula_params(&mut self) -> Result<Vec<Formula>> {
		println!("Parser::parse_formula_params");
		self.expect(TokenKind::Open)?;
		let params = self.parse_formula_list()?;
		self.expect(TokenKind::Close)?;
		Ok(params)
	}

	fn parse_paren_formula(&mut self) -> Result<Formula> {
		println!("Parser::parse_paren_formula");
		self.expect(TokenKind::Open)?;
		let formula = Formula::paren(self.parse_formula()?);
		self.expect(TokenKind::Close)?;
		Ok(formula)
	}

	fn parse_neg_formula(&mut self) -> Result<Formula> {
		println!("Parser::parse_neg_formula");
		self.expect(TokenKind::Minus)?;
		let tok = self.peek?;
		match tok.kind() {
			TokenKind::Open => {
				self.expect(TokenKind::Open)?;
				let formula = Formula::neg(self.parse_formula()?);
				self.expect(TokenKind::Close)?;
				Ok(formula)
			},
			TokenKind::Nat(val) => {
				self.expect(TokenKind::Nat(val))?;
				Ok(Formula::lit(Lit::from_i64( -(val as i64) )))
			},
			_ => self.formula_err(ErrorKind::UnexpectedToken)
		}
	}

	fn parse_or_formula(&mut self) -> Result<Formula> {
		println!("Parser::parse_or_formula");
		self.expect(TokenKind::Plus)?;
		Ok(Formula::or(self.parse_formula_params()?))
	}

	fn parse_and_formula(&mut self) -> Result<Formula> {
		println!("Parser::parse_and_formula");
		self.expect(TokenKind::Star)?;
		Ok(Formula::and(self.parse_formula_params()?))
	}

	fn parse_eq_formula(&mut self) -> Result<Formula> {
		println!("Parser::parse_eq_formula");
		self.expect(TokenKind::Eq)?;
		Ok(Formula::eq(self.parse_formula_params()?))
	}

	fn parse_xor_formula(&mut self) -> Result<Formula> {
		println!("Parser::parse_xor_formula");
		self.expect(TokenKind::Ident(Ident::Xor))?;
		Ok(Formula::xor(self.parse_formula_params()?))
	}

	pub fn parse_dimacs(&mut self) -> Result<Instance> {
		println!("Parser::parse_dimacs");
		self.consume()?;
		self.parse_header()
	}
}

pub fn parse_dimacs(input: &str) -> Result<Instance> {
	Parser::from(input.chars()).parse_dimacs()
}

#[cfg(test)]
mod tests {
	use super::*;

	// #[test]
	// fn simple_cnf() {
	// 	let sample = r"
	// 		c Sample DIMACS .cnf file
	// 		c holding some information
	// 		c and trying to be some
	// 		c kind of a test.
	// 		p cnf 42 1337
	// 		1 2 0
	// 		-3 4 0
	// 		5 -6 7 0
	// 		-7 -8 -9 0";
	// 	let parsed = parse_dimacs(sample).expect("valid .cnf");
	// 	let expected = Instance::cnf(42, vec![
	// 		Clause::from_vec(vec![Lit::from_i64( 1), Lit::from_i64( 2)]),
	// 		Clause::from_vec(vec![Lit::from_i64(-3), Lit::from_i64( 4)]),
	// 		Clause::from_vec(vec![Lit::from_i64( 5), Lit::from_i64(-6), Lit::from_i64( 7)]),
	// 		Clause::from_vec(vec![Lit::from_i64(-7), Lit::from_i64(-8), Lit::from_i64(-9)])
	// 	]);
	// 	assert_eq!(parsed, expected);
	// }

	#[test]
	fn simple_sat() {
		let sample = r"
			c Sample DIMACS .sat file
			p sat 42
			(*(+(1 3 -4)
			+(4)
			+(2 3)))";
		let parsed = parse_dimacs(sample).expect("valid .sat");
		let expected = Instance::sat(42, NONE,
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
