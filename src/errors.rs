
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

	MultipleConfigs,
	MissingConfig,
	VarOutOfBounds,
	TooManyClauses,

	// TODO!
	SelfContradictingClause
}

#[derive(Debug, PartialEq, Eq)]
pub struct DimacsError {
	pub line  : usize,
	pub kind  : ErrorKind,
}

impl DimacsError {
	pub fn new(line: usize, kind: ErrorKind) -> Self {
		DimacsError { line: line, kind: kind }
	}
}

pub type Result<T> = ::std::result::Result<T, DimacsError>;
