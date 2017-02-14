

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Var(pub u64);

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

pub struct Instance {
	num_vars: u64,
	clauses : Box<[Clause]>
}

impl Instance {
	pub fn num_vars(&self) -> u64 {
		self.num_vars
	}

	pub fn clauses(&self) -> &[Clause] {
		&self.clauses
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DimacsItem {
	Comment(Comment),
	Config(Config),
	Clause(Clause),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Config {
	num_vars   : u64,
	num_clauses: u64
}

impl Config {
	pub fn new(num_vars: u64, num_clauses: u64) -> Config {
		Config{
			num_vars   : num_vars,
			num_clauses: num_clauses
		}
	}

	pub fn num_vars(&self) -> u64 {
		self.num_vars
	}

	pub fn num_clauses(&self) -> u64 {
		self.num_clauses
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comment {
	content: Box<str>
}

impl Comment {
	pub fn from_string(content: String) -> Comment {
		Comment{
			content: content.into_boxed_str()
		}
	}

	pub fn from_str(content: &str) -> Comment {
		Comment::from_string(content.to_owned())
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

	pub fn from_slice(lits: &[Lit]) -> Clause {
		Clause::from_vec(lits.to_owned())
	}

	pub fn len(&self) -> usize {
		self.lits.len()
	}

	pub fn lits(&self) -> &[Lit] {
		&self.lits
	}
}
