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

use crate::errors::*;
use crate::items::*;
use crate::lexer::*;

#[derive(Debug, Clone)]
struct Parser<I>
where
    I: Iterator<Item = char>,
{
    tokens: ValidLexer<I>,
    peek: Result<Token>,
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn from(input: I) -> Parser<I> {
        Parser {
            tokens: ValidLexer::from(input),
            peek: Err(ParseError::new(Loc::new(0, 0), ErrorKind::EmptyTokenStream)),
        }
    }

    fn mk_err(&self, kind: ErrorKind) -> ParseError {
        ParseError::new(self.peek_loc(), kind)
    }

    fn err<T>(&self, kind: ErrorKind) -> Result<T> {
        Err(self.mk_err(kind))
    }

    fn peek_loc(&self) -> Loc {
        match self.peek {
            Ok(tok) => tok.loc,
            Err(err) => err.loc,
        }
    }

    fn consume(&mut self) -> Result<Token> {
        self.peek = self
            .tokens
            .next()
            .unwrap_or(Ok(Token::new(self.peek_loc(), TokenKind::EndOfFile)));
        self.peek
    }

    fn expect(&mut self, expected: TokenKind) -> Result<Token> {
        use self::ErrorKind::{UnexpectedEndOfFile, UnexpectedToken};
        use self::TokenKind::EndOfFile;
        match self.peek?.kind {
            k if k == expected => self.consume(),
            EndOfFile => self.err(UnexpectedEndOfFile),
            _ => self.err(UnexpectedToken),
        }
    }

    fn is_at_eof(&self) -> bool {
        match self.peek {
            Ok(peek) => peek.kind == TokenKind::EndOfFile,
            _ => false,
        }
    }

    fn expect_nat(&mut self) -> Result<u64> {
        match self.peek?.kind {
            TokenKind::Nat(val) => {
                self.consume()?;
                Ok(val)
            }
            _ => self.err(ErrorKind::ExpectedNat),
        }
    }

    fn parse_header(&mut self) -> Result<Instance> {
        use self::Ident::*;
        use self::TokenKind::Ident;
        self.expect(Ident(Problem))?;
        match self.peek?.kind {
            Ident(Cnf) => self.parse_cnf_header(),
            Ident(Sat) | Ident(Sate) | Ident(Satx) | Ident(Satex) => self.parse_sat_header(),
            _ => self.err(ErrorKind::UnexpectedToken),
        }
    }

    fn parse_cnf_header(&mut self) -> Result<Instance> {
        self.expect(TokenKind::Ident(Ident::Cnf))?;
        let num_vars = self.expect_nat()?;
        let num_clauses = self.expect_nat()?;
        Ok(Instance::cnf(num_vars, self.parse_clauses(num_clauses)?))
    }

    fn parse_lit(&mut self) -> Result<Lit> {
        match self.peek?.kind {
            TokenKind::Minus => {
                self.consume()?;
                Ok(Lit::from_i64(-(self.expect_nat()? as i64)))
            }
            TokenKind::Nat(val) => {
                self.consume()?;
                Ok(Lit::from_i64(val as i64))
            }
            _ => self.err(ErrorKind::ExpectedLit),
        }
    }

    fn parse_clause(&mut self) -> Result<Clause> {
        use self::ErrorKind::UnexpectedToken;
        use self::TokenKind::{EndOfFile, Minus, Nat, Zero};
        let mut lits = Vec::new();
        loop {
            match self.peek?.kind {
                Minus | Nat(_) => lits.push(self.parse_lit()?),
                Zero | EndOfFile => {
                    self.consume()?;
                    return Ok(Clause::from_vec(lits));
                }
                _ => return self.err(UnexpectedToken),
            }
        }
    }

    fn parse_clauses(&mut self, num_clauses: u64) -> Result<Vec<Clause>> {
        let mut clauses = Vec::with_capacity(num_clauses as usize);
        while !self.is_at_eof() {
            clauses.push(self.parse_clause()?);
        }
        Ok(clauses)
    }

    fn parse_sat_extensions<'a>(&'a mut self) -> Result<Extensions> {
        use self::ErrorKind::*;
        use self::Ident::{Sat, Sate, Satex, Satx};
        use self::TokenKind::Ident;
        match self.peek?.kind {
            Ident(Sat) => {
                self.consume()?;
                Ok(Extensions::NONE)
            }
            Ident(Sate) => {
                self.consume()?;
                Ok(Extensions::EQ)
            }
            Ident(Satx) => {
                self.consume()?;
                Ok(Extensions::XOR)
            }
            Ident(Satex) => {
                self.consume()?;
                Ok(Extensions::EQ | Extensions::XOR)
            }
            _ => self.err(InvalidSatExtension),
        }
    }

    fn parse_sat_header(&mut self) -> Result<Instance> {
        let extensions = self.parse_sat_extensions()?;
        let num_vars = self.expect_nat()?;
        Ok(Instance::sat(
            num_vars,
            extensions,
            self.parse_paren_formula()?,
        ))
    }

    fn parse_formula(&mut self) -> Result<Formula> {
        use crate::lexer::Ident::*;
        use crate::lexer::TokenKind::*;
        let tok = self.peek?;
        match tok.kind {
            Nat(val) => {
                self.consume()?;
                Ok(Formula::lit(Lit::from_i64(val as i64)))
            }
            Open => self.parse_paren_formula(),
            Plus => self.parse_or_formula(),
            Star => self.parse_and_formula(),
            Minus => self.parse_neg_formula(),
            Eq => self.parse_eq_formula(),
            Ident(Xor) => self.parse_xor_formula(),
            _ => self.err(ErrorKind::UnexpectedToken),
        }
    }

    fn parse_formula_list(&mut self) -> Result<Vec<Formula>> {
        let mut formulas = Vec::new();
        while self.peek?.kind != TokenKind::Close {
            formulas.push(self.parse_formula()?);
        }
        Ok(formulas)
    }

    fn parse_formula_params(&mut self) -> Result<Vec<Formula>> {
        self.expect(TokenKind::Open)?;
        let params = self.parse_formula_list()?;
        self.expect(TokenKind::Close)?;
        Ok(params)
    }

    fn parse_paren_formula(&mut self) -> Result<Formula> {
        self.expect(TokenKind::Open)?;
        let formula = Formula::paren(self.parse_formula()?);
        self.expect(TokenKind::Close)?;
        Ok(formula)
    }

    fn parse_neg_formula(&mut self) -> Result<Formula> {
        self.expect(TokenKind::Minus)?;
        let tok = self.peek?;
        match tok.kind {
            TokenKind::Open => {
                self.expect(TokenKind::Open)?;
                let formula = Formula::neg(self.parse_formula()?);
                self.expect(TokenKind::Close)?;
                Ok(formula)
            }
            TokenKind::Nat(val) => {
                self.consume()?;
                Ok(Formula::lit(Lit::from_i64(-(val as i64))))
            }
            _ => self.err(ErrorKind::UnexpectedToken),
        }
    }

    fn parse_or_formula(&mut self) -> Result<Formula> {
        self.expect(TokenKind::Plus)?;
        Ok(Formula::or(self.parse_formula_params()?))
    }

    fn parse_and_formula(&mut self) -> Result<Formula> {
        self.expect(TokenKind::Star)?;
        Ok(Formula::and(self.parse_formula_params()?))
    }

    fn parse_eq_formula(&mut self) -> Result<Formula> {
        self.expect(TokenKind::Eq)?;
        Ok(Formula::eq(self.parse_formula_params()?))
    }

    fn parse_xor_formula(&mut self) -> Result<Formula> {
        self.expect(TokenKind::Ident(Ident::Xor))?;
        Ok(Formula::xor(self.parse_formula_params()?))
    }

    fn parse_dimacs(&mut self) -> Result<Instance> {
        self.consume()?;
        let instance = self.parse_header();
        if self.is_at_eof() {
            instance
        } else {
            self.err(ErrorKind::NotParsedToEnd)
        }
    }
}

/// Parses a the given string as `.cnf` or `.sat` file as specified in
/// [DIMACS format specification](http://www.domagoj-babic.com/uploads/ResearchProjects/Spear/dimacs-cnf.pdf).
///
/// Returns an appropriate SAT instance if no errors occured while parsing.
pub fn parse_dimacs(input: &str) -> Result<Instance> {
    Parser::from(input.chars()).parse_dimacs()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_cnf_1() {
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
        let expected = Instance::cnf(
            42,
            vec![
                Clause::from_vec(vec![Lit::from_i64(1), Lit::from_i64(2)]),
                Clause::from_vec(vec![Lit::from_i64(-3), Lit::from_i64(4)]),
                Clause::from_vec(vec![Lit::from_i64(5), Lit::from_i64(-6), Lit::from_i64(7)]),
                Clause::from_vec(vec![
                    Lit::from_i64(-7),
                    Lit::from_i64(-8),
                    Lit::from_i64(-9),
                ]),
            ],
        );
        assert_eq!(parsed, expected);
    }

    #[test]
    fn simple_cnf_2() {
        let sample = r"
			c Example CNF format file
			c
			p cnf 4 3
			1 3 -4 0
			4 0 2
			-3";
        let parsed = parse_dimacs(sample).expect("valid .cnf");
        let expected = Instance::cnf(
            4,
            vec![
                Clause::from_vec(vec![Lit::from_i64(1), Lit::from_i64(3), Lit::from_i64(-4)]),
                Clause::from_vec(vec![Lit::from_i64(4)]),
                Clause::from_vec(vec![Lit::from_i64(2), Lit::from_i64(-3)]),
            ],
        );
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
        let expected = Instance::sat(
            42,
            Extensions::NONE,
            Formula::paren(Formula::and(vec![
                Formula::or(vec![
                    Formula::lit(Lit::from_i64(1)),
                    Formula::lit(Lit::from_i64(3)),
                    Formula::lit(Lit::from_i64(-4)),
                ]),
                Formula::or(vec![Formula::lit(Lit::from_i64(4))]),
                Formula::or(vec![
                    Formula::lit(Lit::from_i64(2)),
                    Formula::lit(Lit::from_i64(3)),
                ]),
            ])),
        );
        assert_eq!(parsed, expected);
    }
}
