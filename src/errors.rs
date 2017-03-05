
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Loc {
	line: u64,
	col : u64
}

impl Loc {
	pub fn new(line: u64, col: u64) -> Loc {
		Loc{ line: line, col: col }
	}

	pub fn bump_line(&mut self) {
		self.line += 1;
		self.col   = 0;
	}

	pub fn bump_col(&mut self) {
		self.col += 1;
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ErrorKind {
	InvalidTokenStart,
	UnknownKeyword,
	InvalidIdentifier,
	UnexpectedChar,
	UnexpectedToken,
	UnexpectedEndOfFile,
	EmptyTokenStream,
	InvalidSatExtension,
	NotParsedToEnd

	// UnexpectedToken,
	// UnexpectedEndOfLine,
	// InvalidStartOfLine,

	// InvalidConfigNumVars,
	// InvalidConfigNumClauses,
	// TooManyArgsForConfig,
	// TooFewArgsForConfig,

	// InvalidClause,
	// TooFewArgsForClause,
	// MissingZeroLiteralAtEndOfClause,
	// InvalidClauseLit,

	// MultipleConfigs, // enhanced check
	// MissingConfig, // enhanced check
	// VarOutOfBounds,
	// TooManyClauses, // enhanced check

	// InvalidInteger,
	// UnexpectedNegativeInteger,

	// // TODO!
	// SelfContradictingClause, // enhanced check
	// NonUsedVarsFound // enhanced check
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ParseError {
	pub loc : Loc,
	pub kind: ErrorKind,
}

impl ParseError {
	pub fn new(loc: Loc, kind: ErrorKind) -> Self {
		ParseError { loc: loc, kind: kind }
	}
}

pub type Result<T> = ::std::result::Result<T, ParseError>;
