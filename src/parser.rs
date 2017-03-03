
// #[derive(Debug, Clone)]
// pub struct DimacsParser<I>
// 	where I: Iterator<Item=char>
// {
// 	input: Peekable<I>,
// 	loc  : Loc
// }

// #[derive(Debug, Clone)]
// pub struct CnfParser<I>
// 	where I: Iterator<Item=char>
// {
// 	parser : DimacsParser<I>,
// 	clauses: Vec<Clause>
// }

// #[derive(Debug, Clone)]
// pub struct SatParser<I>
// 	where I: Iterator<Item=char>
// {
// 	parser : DimacsParser<I>,
// 	formula: Formula
// }

// impl<I> DimacsParser<I>
// 	where I: Iterator<Item=char>
// {
// 	pub fn from_input(input: I) -> DimacsParser<I> {
// 		DimacsParser{
// 			input: input.peekable(),
// 			loc  : Loc::new(0, 0)
// 		}
// 	}

// 	fn parse_header(&mut self) -> Result<Problem> {
// 		Ok(Problem::cnf(0, 0)) // TODO!
// 	}

// 	fn parse_clauses(&mut self) -> Result<Vec<Clause>> {
// 		Ok(vec![]) // TODO!
// 	}

// 	fn parse_formula(&mut self) -> Result<Formula> {
// 		Ok(Formula::Lit(Lit::from_i64(0))) // TODO!
// 	}

// 	fn bump(&mut self) -> Option<char> {
// 		self.input.next();
// 		if let Some(&peeked) = self.input.peek() {
// 			self.peek = peeked;
// 			if peeked == '\n' {
// 				self.line += 1;
// 				self.col   = 1;
// 			}
// 			else {
// 				self.col += 1;
// 			}
// 			Some(peeked)
// 		}
// 		else {
// 			None
// 		}
// 	}

// 	pub fn parse_dimacs(&mut self) -> Instance {
// 		let _ = self.parse_header();
// 		let _ = self.parse_clauses();
// 		let _ = self.parse_formula();
// 		Instance::cnf(0, vec![])
// 	}
// }
