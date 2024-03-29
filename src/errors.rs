//! Defines some error kinds and facilities to communicate errors while parsing
//! `.cnf` or `.sat` files.

use std::{error, fmt};

/// Represents a source line and column of an error.
/// Used to provide the user of this parser facility with necesary information
/// to debug their input files formats.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Loc {
    line: u64,
    col: u64,
}

impl Loc {
    /// Creates a new location with a given line and column.
    pub fn new(line: u64, col: u64) -> Loc {
        Loc {
            line: line,
            col: col,
        }
    }

    /// Bumps the line of this location, resetting its column.
    pub fn bump_line(&mut self) {
        self.line += 1;
        self.col = 0;
    }

    /// Bumps the column of this location.
    pub fn bump_col(&mut self) {
        self.col += 1;
    }
}

impl fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

/// Different kinds of errors that may occure while parsing.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    /// When parsing an invalid character at the start of a token.
    InvalidTokenStart,

    /// When parsing an unknown keyword (e.g. "foo").
    UnknownKeyword,

    /// When lexing an unexpected character.
    UnexpectedChar,

    /// When parsing an unexpected token.
    UnexpectedToken,

    /// When detecting an unexpected end of file.
    UnexpectedEndOfFile,

    /// When tried to parse an empty string.
    EmptyTokenStream,

    /// When parsing an unknown SAT extension.
    InvalidSatExtension,

    /// When the parser is not at the end of file when finished parsing.
    NotParsedToEnd,

    /// When a natural number was expected but not found.
    ExpectedNat,

    /// When a literal was expected but not found.
    ExpectedLit, // IllegalXorExtensionUsed, // enhanced check
                 // IllegalEqExtensionUsed, // enhanced check

                 // TooManyVariables, // enhanced check
                 // TooManyClauses, // enhanced check
                 // SelfContradictingClause, // enhanced check
}

/// Represents an error that occured while parsing.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// The source location (line + column) of the error.
    pub loc: Loc,

    /// The kind of the error that occured.
    pub kind: ErrorKind,
}

impl ParseError {
    /// Creates a new parser error at the given source location with the given error kind.
    pub fn new(loc: Loc, kind: ErrorKind) -> Self {
        ParseError {
            loc: loc,
            kind: kind,
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            ErrorKind::InvalidTokenStart => write!(f, "invalid token start at {}", self.loc),
            ErrorKind::UnknownKeyword => write!(f, "unknown keyword at {}", self.loc),
            ErrorKind::UnexpectedChar => write!(f, "unexpected character at {}", self.loc),
            ErrorKind::UnexpectedToken => write!(f, "unexpected token at {}", self.loc),
            ErrorKind::UnexpectedEndOfFile => write!(f, "unexpected end of file at {}", self.loc),
            ErrorKind::EmptyTokenStream => write!(f, "empty token stream"),
            ErrorKind::InvalidSatExtension => write!(f, "invalid sat extension"),
            ErrorKind::NotParsedToEnd => write!(f, "not parsed to end"),
            ErrorKind::ExpectedNat => write!(f, "expected natural number at {}", self.loc),
            ErrorKind::ExpectedLit => write!(f, "expected literal at {}", self.loc),
        }
    }
}

impl error::Error for ParseError {}

/// The result type used within this crate while parsing.
pub type Result<T> = ::std::result::Result<T, ParseError>;
