
#[derive(Debug, PartialEq, Eq)]
pub enum ErrorKind {
	UnexpectedToken,
	UnexpectedEndOfLine,
	InvalidStartOfLine,

	InvalidConfigNumVars,
	InvalidConfigNumClauses,
	TooManyArgsForConfig,
	TooFewArgsForConfig,

	InvalidClause,
	TooFewArgsForClause,
	MissingZeroLiteralAtEndOfClause,
	InvalidClauseLit,

	MultipleConfigs, // enhanced check
	MissingConfig, // enhanced check
	VarOutOfBounds,
	TooManyClauses, // enhanced check

	InvalidInteger,
	UnexpectedNegativeInteger,

	// TODO!
	SelfContradictingClause, // enhanced check
	NonUsedVarsFound // enhanced check
}

#[derive(Debug, PartialEq, Eq)]
pub struct DimacsError {
	pub line  : usize,
	pub col   : usize,
	pub kind  : ErrorKind,
}

impl DimacsError {
	pub fn new(line: usize, col: usize, kind: ErrorKind) -> Self {
		DimacsError { line: line, col: col, kind: kind }
	}
}

pub type Result<T> = ::std::result::Result<T, DimacsError>;
