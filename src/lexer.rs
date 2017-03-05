use ::errors::*;

use ::errors::ErrorKind::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Token {
	loc : Loc,
	kind: TokenKind
}

impl Token {
	pub fn new(loc: Loc, kind: TokenKind) -> Token {
		Token{
			loc : loc,
			kind: kind
		}
	}

	pub fn loc(self) -> Loc {
		self.loc
	}

	pub fn kind(self) -> TokenKind {
		self.kind
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TokenKind {
	/// Represents an entire 'c foo bar\n' line
	Comment,

	/// Represents a positive, non-zero integer value, e.g. 42
	Nat(u64),

	/// Represents a zero integer value
	Zero,

	/// Represents a '+' symbol, interpreted as logical or
	Plus,

	/// Represents a '-' symbol, interpreted as logical negation for literals or formulas
	Minus, // TODO!

	/// Represents a '*' symbol, interpreted as logical and
	Star,

	/// Represents a '=' symbol, interpreted as logical equal
	Eq,

	/// Represents an opening parentheses '('
	Open,

	/// Represents a closed parentheses ')'
	Close,

	/// Represents a known keyword, e.g. cnf, sat, sate, satex
	Ident(Ident),

	/// Represents the end of a file
	EndOfFile
}
use self::TokenKind::*;

impl TokenKind {
	pub fn is_relevant(self) -> bool {
		match self {
			Comment => false,
			_       => true
		}
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Ident {
	/// Represents a 'p' keyword
	Problem,

	/// Used in 'satx' or 'satex' extension formulas.
	Xor,

	/// Used as problem-kind parameter in problem lines to denote a CNF problem.
	Cnf,

	/// Used as problem-kind parameter in problem lines to denote a SAT problem.
	Sat,

	/// Used as problem-kind parameter in problem lines to denote a CNF problem with the Xor extension.
	Satx,

	/// Used as problem-kind parameter in problem lines to denote a CNF problem with the Eq extension.
	Sate,

	/// Used as problem-kind parameter in problem lines to denote a CNF problem with the Eq and Xor extensions.
	Satex
}
use self::Ident::*;

#[derive(Debug, Clone)]
pub struct Lexer<I>
	where I: Iterator<Item=char>
{
	/// input iterator
	input : I,

	/// internal buffer to map to known keywords
	buffer: String,

	/// the current character that is being dispatched upon
	peek  : char,

	/// represents the `Loc` of the next iterated item
	nloc  : Loc,

	/// represents the current `Loc` within the stream
	cloc  : Loc
}

impl<I> Lexer<I>
	where I: Iterator<Item=char>
{
	pub fn from(input: I) -> Lexer<I> {
		let mut lex = Lexer{
			input : input,
			buffer: String::new(),
			peek  : '\0',
			nloc  : Loc::new(1, 0),
			cloc  : Loc::new(1, 0)
		};
		lex.bump();
		lex
	}

	fn bump_opt(&mut self) -> Option<char> {
		if let Some(peeked) = self.input.next() {
			self.peek = peeked;
			if peeked == '\n' {
				self.cloc.bump_line()
			}
			else {
				self.cloc.bump_col()
			}
			Some(peeked)
		}
		else {
			None
		}
	}

	fn bump(&mut self) -> char {
		self.peek = self.bump_opt().unwrap_or('\0');
		self.peek 
	}

	fn mk_token(&self, kind: TokenKind) -> Token {
		Token::new(self.nloc, kind)
	}

	fn mk_error(&self, kind: ErrorKind) -> ParseError {
		ParseError::new(self.nloc, kind)
	}

	fn tok(&self, kind: TokenKind) -> Result<Token> {
		Ok(self.mk_token(kind))
	}

	fn bump_tok(&mut self, kind: TokenKind) -> Result<Token> {
		self.bump();
		self.tok(kind)
	}

	fn err(&self, kind: ErrorKind) -> Result<Token> {
		Err(self.mk_error(kind))
	}

	fn skip_line(&mut self) {
		while self.peek != '\n' && self.peek != '\0' {
			self.bump();
		}
	}

	fn scan_comment(&mut self) -> Result<Token> {
		self.skip_line();
		self.tok(Comment)
	}

	fn scan_ident(&mut self) -> Result<Token> {
		self.buffer.clear();
		self.buffer.push(self.peek);
		while self.bump().is_alphanumeric() {
			self.buffer.push(self.peek);
		}
		match self.buffer.as_str() {
			"c"     => self.scan_comment(),
			"p"     => self.tok(Ident(Problem)),
			"cnf"   => self.tok(Ident(Cnf)),
			"sat"   => self.tok(Ident(Sat)),
			"sate"  => self.tok(Ident(Sate)),
			"satx"  => self.tok(Ident(Satx)),
			"satex" => self.tok(Ident(Satex)),
			"xor"   => self.tok(Ident(Xor)),
			_       => self.err(UnknownKeyword)
		}
	}

	fn skip_ident(&mut self) -> Result<Token> {
		while self.bump().is_alphanumeric() {}
		self.err(InvalidIdentifier)
	}

	fn scan_nat(&mut self) -> Result<Token> {
		let mut val = self.peek.to_digit(10)
			.expect("expected a digit to base 10: (0...9)") as u64;
		while let Some(parsed) = self.bump().to_digit(10) {
			val *= 10;
			val += parsed as u64;
		}
		self.tok(Nat(val))
	}

	fn skip_whitespace(&mut self) {
		while self.peek.is_whitespace() {
			self.bump();
		}
	}

	fn update_nloc(&mut self) {
		self.nloc = self.cloc;
	}

	fn next_token(&mut self) -> Option<Result<Token>> {
		self.skip_whitespace();
		if self.peek == '\0' { return None; }
		self.update_nloc();
		Some(
			match self.peek {
				'a'...'z' => self.scan_ident(),
				'A'...'Z' => self.skip_ident(),

				'1'...'9' => self.scan_nat(),

				'0' => self.bump_tok(Zero),
				'(' => self.bump_tok(Open),
				')' => self.bump_tok(Close),
				'+' => self.bump_tok(Plus),
				'*' => self.bump_tok(Star),
				'=' => self.bump_tok(Eq),
				'-' => self.bump_tok(Minus),

				_ => {
					self.bump();
					self.err(InvalidTokenStart)
				}
			}
		)
	}
}

impl<I> Iterator for Lexer<I>
	where I: Iterator<Item=char>
{
	type Item = Result<Token>;

	fn next(&mut self) -> Option<Self::Item> {
		self.next_token()
	}
}

#[derive(Debug, Clone)]
pub struct ValidLexer<I>
	where I: Iterator<Item=char>
{
	input: Lexer<I>
}

impl<I> ValidLexer<I>
	where I: Iterator<Item=char>
{
	pub fn from(input: I) -> ValidLexer<I> {
		ValidLexer{ input: Lexer::from(input) }
	}
}

impl<I> Iterator for ValidLexer<I>
	where I: Iterator<Item=char>
{
	type Item = Result<Token>;

	fn next(&mut self) -> Option<Self::Item> {
		match self.input.next() {
			None => None,
			Some(res_tok) => match res_tok {
				Err(err) => Some(Err(err)),
				Ok(tok)  => if tok.kind().is_relevant() {
					Some(Ok(tok))
				}
				else {
					self.next()
				}
			}
		}
	}
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
		let mut lexer = Lexer::from(sample.chars());

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(2, 4), Comment))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(3, 4), Comment))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 4), Comment))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(5, 4), Comment))));

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6, 4), Ident(Problem)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6, 6), Ident(Cnf)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6, 10), Nat(42)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6, 13), Nat(1337)))));

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(7, 4), Nat(1)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(7, 6), Nat(2)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(7, 8), Zero))));

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(8, 4), Minus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(8, 5), Nat(3)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(8, 7), Nat(4)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(8, 9), Zero))));

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(9,  4), Nat(5)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(9,  6), Minus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(9,  7), Nat(6)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(9,  9), Nat(7)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(9, 11), Zero))));

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(10,  4), Minus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(10,  5), Nat(7)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(10,  7), Minus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(10,  8), Nat(8)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(10, 10), Minus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(10, 11), Nat(9)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(10, 13), Zero))));

		assert_eq!(lexer.next(), None);
	}

	#[test]
	fn simple_sat() {
		let sample = r"
			c Sample DIMACS .sat file
			p sat 42 1337
			(*(+(1 3 -4)
			+(4)
			+(2 3)))";
		let mut lexer = Lexer::from(sample.chars());

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(2,  4), Comment))));

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(3,  4), Ident(Problem)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(3,  6), Ident(Sat)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(3, 10), Nat(42)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(3, 13), Nat(1337)))));

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 4), Open))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 5), Star))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 6), Open))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 7), Plus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 8), Open))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 9), Nat(1)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 11), Nat(3)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 13), Minus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 14), Nat(4)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 15), Close))));

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(5, 4), Plus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(5, 5), Open))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(5, 6), Nat(4)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(5, 7), Close))));

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6,  4), Plus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6,  5), Open))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6,  6), Nat(2)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6,  8), Nat(3)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6,  9), Close))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6, 10), Close))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6, 11), Close))));

		assert_eq!(lexer.next(), None);
	}

	#[test]
	fn tricky_1() {
		let sample = r"(1-2)";
		let mut lexer = Lexer::from(sample.chars());

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 1), Open))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 2), Nat(1)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 3), Minus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 4), Nat(2)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 5), Close))));

		assert_eq!(lexer.next(), None);
	}

	#[test]
	fn all_idents() {
		let sample = r"p cnf sat satx sate satex xor";
		let mut lexer = Lexer::from(sample.chars());

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 1), Ident(Problem)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 3), Ident(Cnf)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 7), Ident(Sat)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 11), Ident(Satx)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 16), Ident(Sate)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 21), Ident(Satex)))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 27), Ident(Xor)))));

		assert_eq!(lexer.next(), None);
	}

	#[test]
	fn all_ops() {
		let sample = r"()+-*=";
		let mut lexer = Lexer::from(sample.chars());

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 1), Open))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 2), Close))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 3), Plus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 4), Minus))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 5), Star))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(1, 6), Eq))));

		assert_eq!(lexer.next(), None);
	}

	#[test]
	fn invalid_token_start() {
		let sample = r"# foo Big";
		let mut lexer = Lexer::from(sample.chars());

		assert_eq!(lexer.next(), Some(Err(ParseError::new(Loc::new(1, 1), InvalidTokenStart))));
		assert_eq!(lexer.next(), Some(Err(ParseError::new(Loc::new(1, 3), UnknownKeyword))));
		assert_eq!(lexer.next(), Some(Err(ParseError::new(Loc::new(1, 7), InvalidIdentifier))));

		assert_eq!(lexer.next(), None);
	}

	#[test]
	fn only_comments() {
		let sample = r"
			c This is a comment.
			c Just like this.
			c That has to be filtered.
			c But not the following ...
			c Filter this, too!
			c And this!";
		let mut lexer = Lexer::from(sample.chars());

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(2, 4), Comment))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(3, 4), Comment))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(4, 4), Comment))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(5, 4), Comment))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6, 4), Comment))));
		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(7, 4), Comment))));

		assert_eq!(lexer.next(), None);
	}

	#[test]
	fn filter_valid() {
		let sample = r"
			c This is a comment.
			c Just like this.
			c That has to be filtered.
			c But not the following ...
			42
			c Filter this, too!
			INVALID
			c And this!
		";
		let mut lexer = ValidLexer::from(sample.chars());

		assert_eq!(lexer.next(), Some(Ok(Token::new(Loc::new(6, 4), Nat(42)))));
		assert_eq!(lexer.next(), Some(Err(ParseError::new(Loc::new(8, 4), InvalidIdentifier))));

		assert_eq!(lexer.next(), None);
	}
}
