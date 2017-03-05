//! Some item definitions used in instances to provide a virtual representative
//! structure of `.cnf` or `.sat` files and their associated clauses or formula.

/// Represents a variable within a SAT instance.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Var(pub u64);

impl Var {
	/// Converts a variable into its representative `u64` value.
	pub fn to_u64(self) -> u64 { self.0 }
}

/// Represents the sign of a literal.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Sign {
	/// Positive sign.
	Pos,

	/// Negative sign.
	Neg
}

/// Represents a literal within clauses of formulas of a SAT instance.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Lit(i64);

impl Lit {
	/// Returns the underlying `i64` representant of this literal.
	pub fn from_i64(val: i64) -> Lit { Lit(val) }

	/// Returns the associated variable for this literal.
	pub fn var(self) -> Var { Var(self.0.abs() as u64) }

	/// Returns the sign of this literal.
	pub fn sign(self) -> Sign {
		match self.0 >= 0 {
			true => Sign::Pos,
			_    => Sign::Neg
		}
	}
}

/// Represents a clause instance within a `.cnf` file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
	lits: Box<[Lit]>
}

impl Clause {
	/// Creates a new clause from a vector of literals.
	pub fn from_vec(lits: Vec<Lit>) -> Clause {
		Clause{
			lits: lits.into_boxed_slice()
		}
	}

	/// Returns the number of literals of this clause.
	pub fn len(&self) -> usize {
		self.lits.len()
	}

	/// Returns a slice over the literals of this clause.
	pub fn lits(&self) -> &[Lit] {
		&self.lits
	}
}

/// An indirection to a `Formula` via `Box`.
pub type FormulaBox  = Box<Formula>;

/// An immutable list of `Formula`s.
pub type FormulaList = Box<[Formula]>;

/// Represents the structure of formulas of `.sat` files.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
	/// A single literal. This is the leaf node type of sat formulas.
	Lit(Lit),

	/// Represents `(f)` if `f` is a valid formula.
	Paren(FormulaBox),

	/// Represents `-(f)` if `f` is a valid formula.
	/// This negates the result of the inner `f`.
	Neg(FormulaBox),

	/// Represents `*(f_1 .. f_k)` if `f_1, .., f_k` are valid formulas.
	/// The effect is a logical and of its inner formulas.
	And(FormulaList),

	/// Represents `+(f_1 .. f_k)` if `f_1, .., f_k` are valid formulas.
	/// The effect is a logical or of its inner formulas.
	Or(FormulaList),

	/// Represents `xor(f_1 .. f_k)` if `f_1, .., f_k` are valid formulas.
	/// The effect is a logical xor of its inner formulas.
	Xor(FormulaList),

	/// Represents `=(f_1 .. f_k)` if `f_1, .., f_k` are valid formulas.
	/// The effect is a logical equals of its inner formulas.
	Eq(FormulaList)
}

impl Formula {
	/// Creates a new literal leaf formula with the given literal.
	pub fn lit(lit: Lit) -> Formula {
		Formula::Lit(lit)
	}

	/// Wraps the inner formula within parentheses.
	pub fn paren(inner: Formula) -> Formula {
		Formula::Paren(Box::new(inner))
	}

	/// Negates the inner formula.
	pub fn neg(inner: Formula) -> Formula {
		Formula::Neg(Box::new(inner))
	}

	/// Creates a logical and formula of all given formulas in `param`.
	pub fn and(params: Vec<Formula>) -> Formula {
		Formula::And(params.into_boxed_slice())
	}

	/// Creates a logical or formula of all given formulas in `param`.
	pub fn or(params: Vec<Formula>) -> Formula {
		Formula::Or(params.into_boxed_slice())
	}

	/// Creates a logical xor formula of all given formulas in `param`.
	pub fn xor(params: Vec<Formula>) -> Formula {
		Formula::Xor(params.into_boxed_slice())
	}

	/// Creates a logical equality formula of all given formulas in `param`.
	pub fn eq(params: Vec<Formula>) -> Formula {
		Formula::Eq(params.into_boxed_slice())
	}
}

/// Represents a SAT instance for `.cnf` or `.sat` files.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instance {
	/// A `.cnf` SAT instance with clauses.
	Cnf{
		/// The number of unique variables used within this `.cnf` SAT instance.
		num_vars: u64,

		/// The clauses within this `.cnf` SAT instance formula.
		clauses: Box<[Clause]>
	},

	/// A `.sat` SAT instance with an underlying formula and extensions.
	Sat{
		/// The number of unique variables used within this `.sat` SAT instance.
		num_vars: u64,

		/// Extensions (e.g. `XOR` or `EQ`) being used in this SAT instance.
		extensions: Extensions,

		/// The underlying formula of this SAT instance.
		formula: Formula
	}
}

impl Instance {
	/// Creates a new SAT instance for `.cnf` files with given clauses.
	pub fn cnf(num_vars: u64, clauses: Vec<Clause>) -> Instance {
		Instance::Cnf{num_vars: num_vars, clauses: clauses.into_boxed_slice()}
	}

	/// Creates a new SAT instance for `.sat` files with given extensions and an underlying formula.
	pub fn sat(num_vars: u64, extensions: Extensions, formula: Formula) -> Instance {
		Instance::Sat{num_vars: num_vars, extensions: extensions, formula: formula}
	}
}

bitflags! {
	/// Possible extensions for `.sat` file SAT instances.
    pub flags Extensions: u32 {
    	/// If no extensions are being used.
    	const NONE = 0b00000000,
    	/// If the XOR-Extension is being used to allow for `xor(..)` formulas.
        const XOR  = 0b00000001,
        /// If the EQ-Extension is being used to allow for `=(..)` formulas.
        const EQ   = 0b00000010
    }
}
