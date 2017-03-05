
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

type FormulaBox  = Box<Formula>;
type FormulaList = Box<[Formula]>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
	Lit(Lit),
	Paren(FormulaBox),
	Neg(FormulaBox),
	And(FormulaList),
	Or(FormulaList),
	Xor(FormulaList),
	Eq(FormulaList)
}

impl Formula {
	pub fn lit(lit: Lit) -> Formula {
		Formula::Lit(lit)
	}

	pub fn paren(inner: Formula) -> Formula {
		Formula::Paren(Box::new(inner))
	}

	pub fn neg(inner: Formula) -> Formula {
		Formula::Neg(Box::new(inner))
	}

	pub fn and(params: Vec<Formula>) -> Formula {
		Formula::And(params.into_boxed_slice())
	}

	pub fn or(params: Vec<Formula>) -> Formula {
		Formula::Or(params.into_boxed_slice())
	}

	pub fn xor(params: Vec<Formula>) -> Formula {
		Formula::Xor(params.into_boxed_slice())
	}

	pub fn eq(params: Vec<Formula>) -> Formula {
		Formula::Eq(params.into_boxed_slice())
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instance {
	Cnf{
		num_vars: u64,
		clauses: Box<[Clause]>
	},
	Sat{
		num_vars: u64,
		extensions: Extensions,
		formula: Formula
	}
}

impl Instance {
	pub fn cnf(num_vars: u64, clauses: Vec<Clause>) -> Instance {
		Instance::Cnf{num_vars: num_vars, clauses: clauses.into_boxed_slice()}
	}

	pub fn sat(num_vars: u64, extensions: Extensions, formula: Formula) -> Instance {
		Instance::Sat{num_vars: num_vars, extensions: extensions, formula: formula}
	}

	// pub fn sat(num_vars: u64, formula: Formula) -> Instance {
	// 	Instance::sat_with_ext(num_vars, vec![], formula)
	// }

	// pub fn satx(num_vars: u64, formula: Formula) -> Instance {
	// 	Instance::sat_with_ext(num_vars, vec![Extension::Xor], formula)
	// }

	// pub fn sate(num_vars: u64, formula: Formula) -> Instance {
	// 	Instance::sat_with_ext(num_vars, vec![Extension::Eq], formula)
	// }

	// pub fn satex(num_vars: u64, formula: Formula) -> Instance {
	// 	Instance::sat_with_ext(num_vars, vec![Extension::Eq, Extension::Xor], formula)
	// }
}

// #[derive(Debug, Copy, Clone, PartialEq, Eq)]
// pub enum Extension {
// 	Xor,
// 	Eq
// }

bitflags! {
    pub flags Extensions: u32 {
    	const NONE = 0b00000000,
        const XOR  = 0b00000001,
        const EQ   = 0b00000010
    }
}

// #[derive(Debug, Copy, Clone, PartialEq, Eq)]
// pub struct Extensions(Extension);

// impl Extensions {
// 	pub fn none() -> Extensions {
// 		Extensions(None)
// 	}

// 	pub fn from(ext: Extension) -> Extensions {}

// 	pub fn xor() -> Extensions {
// 		Extensions(Xor)
// 	}

// 	pub fn eq() -> Extensions {
// 		Extensions(Eq)
// 	}

// 	pub fn with_xor(self) -> Extensions {
// 		Extensions(self.0 | Xor)
// 	}

// 	pub fn with_eq(self) -> Extensions {
// 		Extensions(self.0 | Eq)
// 	}

// 	pub fn supports_xor(self) -> bool {
// 		self.0.contains(Xor)
// 	}

// 	pub fn supports_eq(self) -> bool {
// 		self.0.contains(Eq)
// 	}
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum Problem {
// 	Cnf{num_vars: u64, num_clauses: u64},
// 	Sat{num_vars: u64, extensions: Box<[Extension]>},
// }

// impl Problem {
// 	pub fn cnf(num_vars: u64, num_clauses: u64) -> Problem {
// 		Problem::Cnf{
// 			num_vars: num_vars,
// 			num_clauses: num_clauses
// 		}
// 	}

// 	fn with_extensions(num_vars: u64, extensions: &[Extension]) -> Problem {
// 		Problem::Sat{
// 			num_vars: num_vars,
// 			extensions: extensions.to_vec().into_boxed_slice()
// 		}
// 	}

// 	pub fn sat(num_vars: u64) -> Problem {
// 		Problem::with_extensions(num_vars, &[])
// 	}

// 	pub fn sat_eq(num_vars: u64) -> Problem {
// 		Problem::with_extensions(num_vars, &[Extension::Eq])
// 	}

// 	pub fn sat_xor(num_vars: u64) -> Problem {
// 		Problem::with_extensions(num_vars, &[Extension::Xor])
// 	}

// 	pub fn sat_ex(num_vars: u64) -> Problem {
// 		Problem::with_extensions(num_vars, &[Extension::Eq, Extension::Xor])
// 	}

// 	pub fn has_extension(&self, ext: Extension) -> bool {
// 		match self {
// 			&Problem::Cnf{..} => false,
// 			&Problem::Sat{ref extensions, ..} => extensions.contains(&ext)
// 		}
// 	}
// }
