
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Var(pub u64);

impl Var {
	pub fn to_u64(self) -> u64 { self.0 }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Sign { Pos, Neg }

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Lit(i64);

impl Lit {
	pub fn from_i64(val: i64) -> Lit { Lit(val) }
	pub fn var(self) -> Var { Var(self.0.abs() as u64) }
	pub fn sign(self) -> Sign {
		match self.0 >= 0 {
			true => Sign::Pos,
			_    => Sign::Neg
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
	lits: Box<[Lit]>
}

impl Clause {
	pub fn from_vec(lits: Vec<Lit>) -> Clause {
		Clause{
			lits: lits.into_boxed_slice()
		}
	}

	pub fn len(&self) -> usize {
		self.lits.len()
	}

	pub fn lits(&self) -> &[Lit] {
		&self.lits
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
	Lit(Lit),
	Paren(Box<Formula>),
	Neg(Box<Formula>),
	And(Box<[Formula]>),
	Or(Box<[Formula]>),
	Xor(Box<[Formula]>),
	Equals(Box<[Formula]>)
}

// #[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instance {
	Cnf{
		num_vars: u64,
		clauses: Box<[Clause]>
	},
	Sat{
		num_vars: u64,
		formula: Formula
	}
}

impl Instance {
	pub fn cnf(num_vars: u64, clauses: Vec<Clause>) -> Instance {
		Instance::Cnf{num_vars: num_vars, clauses: clauses.into_boxed_slice()}
	}

	pub fn sat(num_vars: u64, formula: Formula) -> Instance {
		Instance::Sat{num_vars: num_vars, formula: formula}
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Extension {
	Xor,
	Equals
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Problem {
	Cnf{num_vars: u64, num_clauses: u64},
	Sat{num_vars: u64, extensions: Box<[Extension]>},
}

impl Problem {
	pub fn cnf(num_vars: u64, num_clauses: u64) -> Problem {
		Problem::Cnf{
			num_vars: num_vars,
			num_clauses: num_clauses
		}
	}

	fn with_extensions(num_vars: u64, extensions: &[Extension]) -> Problem {
		Problem::Sat{
			num_vars: num_vars,
			extensions: extensions.to_vec().into_boxed_slice()
		}
	}

	pub fn sat(num_vars: u64) -> Problem {
		Problem::with_extensions(num_vars, &[])
	}

	pub fn sat_eq(num_vars: u64) -> Problem {
		Problem::with_extensions(num_vars, &[Extension::Equals])
	}

	pub fn sat_xor(num_vars: u64) -> Problem {
		Problem::with_extensions(num_vars, &[Extension::Xor])
	}

	pub fn sat_ex(num_vars: u64) -> Problem {
		Problem::with_extensions(num_vars, &[Extension::Equals, Extension::Xor])
	}

	pub fn has_extension(&self, ext: Extension) -> bool {
		match self {
			&Problem::Cnf{..} => false,
			&Problem::Sat{ref extensions, ..} => extensions.contains(&ext)
		}
	}
}
