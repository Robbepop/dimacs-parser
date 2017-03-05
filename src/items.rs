
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
}

bitflags! {
    pub flags Extensions: u32 {
    	const NONE = 0b00000000,
        const XOR  = 0b00000001,
        const EQ   = 0b00000010
    }
}
