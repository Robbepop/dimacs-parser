//! Some item definitions used in instances to provide a virtual representative
//! structure of `.cnf` or `.sat` files and their associated clauses or formula.

use std::string::ToString;

/// Represents a variable within a SAT instance.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Var(pub u64);

impl Var {
    /// Converts a variable into its representative `u64` value.
    pub fn to_u64(self) -> u64 {
        self.0
    }
}

impl ToString for Var {
    fn to_string(&self) -> String {
        self.to_u64().to_string()
    }
}

/// Represents the sign of a literal.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Sign {
    /// Positive sign.
    Pos,

    /// Negative sign.
    Neg,
}

impl ToString for Sign {
    fn to_string(&self) -> String {
        match self {
            Sign::Pos => String::from(""),
            Sign::Neg => String::from("-")
        }
    }
}

/// Represents a literal within clauses of formulas of a SAT instance.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Lit(i64);

impl Lit {
    /// Returns the underlying `i64` representant of this literal.
    pub fn from_i64(val: i64) -> Lit {
        Lit(val)
    }

    /// Returns the associated variable for this literal.
    pub fn var(self) -> Var {
        Var(self.0.abs() as u64)
    }

    /// Returns the inner `i64` value.
    pub fn to_i64(self) -> i64 {
        self.0
    }

    /// Returns the sign of this literal.
    pub fn sign(self) -> Sign {
        match self.0 >= 0 {
            true => Sign::Pos,
            _ => Sign::Neg,
        }
    }
}

impl ToString for Lit {
    fn to_string(&self) -> String {
        self.to_i64().to_string()
    }
}


/// Represents a clause instance within a `.cnf` file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    lits: Box<[Lit]>,
}

impl Clause {
    /// Creates a new clause from a vector of literals.
    pub fn from_vec(lits: Vec<Lit>) -> Clause {
        Clause {
            lits: lits.into_boxed_slice(),
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
pub type FormulaBox = Box<Formula>;

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
    Eq(FormulaList),
}

impl ToString for Formula {
    fn to_string(&self) -> String {
        let fl_to_string = |fl: &FormulaList| {
            let fv: Vec<String> = fl.iter().map(|x| x.to_string()).collect();
            fv.join(" ")
        };
        match self {
            Formula::Lit(l) => l.to_string(),
            Formula::Paren(f) => format!("({})", f.to_string()),
            Formula::Neg(f) => format!("-{}", f.to_string()),
            Formula::And(fl) => format!("*({})", fl_to_string(fl)),
            Formula::Or(fl) => format!("+({})", fl_to_string(fl)),
            Formula::Xor(fl) => format!("xor({})", fl_to_string(fl)),
            Formula::Eq(fl) => format!("=({})", fl_to_string(fl)),
        }
    }
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
    Cnf {
        /// The number of unique variables used within this `.cnf` SAT instance.
        num_vars: u64,

        /// The clauses within this `.cnf` SAT instance formula.
        clauses: Box<[Clause]>,
    },

    /// A `.sat` SAT instance with an underlying formula and extensions.
    Sat {
        /// The number of unique variables used within this `.sat` SAT instance.
        num_vars: u64,

        /// Extensions (e.g. `XOR` or `EQ`) being used in this SAT instance.
        extensions: Extensions,

        /// The underlying formula of this SAT instance.
        formula: Formula,
    },
}

impl ToString for Instance {
    fn to_string(&self) -> String {
        match self {
            Instance::Cnf {num_vars, clauses} =>
                Instance::cnf_to_string(*num_vars, clauses),
            Instance::Sat {num_vars, extensions, formula} => {
                Instance::sat_to_string(*num_vars, extensions, formula)
            },
        }

    }
}

impl Instance {
    /// Creates a new SAT instance for `.cnf` files with given clauses.
    pub fn cnf(num_vars: u64, clauses: Vec<Clause>) -> Instance {
        Instance::Cnf {
            num_vars,
            clauses: clauses.into_boxed_slice(),
        }
    }

    /// Creates a new SAT instance for `.sat` files with given extensions and
    /// an underlying formula.
    pub fn sat(num_vars: u64, extensions: Extensions, formula: Formula) -> Instance {
        Instance::Sat {
            num_vars,
            extensions,
            formula,
        }
    }

    fn sat_to_string(num_vars: u64, extensions: &Extensions,
                     formula: &Formula) -> String {
        let problem = format!("p {} {}", extensions.to_string(), num_vars);
        let formula = formula.to_string();
        format!("{}\n{}\n", problem, formula)
    }

    fn cnf_to_string(num_vars: u64, clauses: &Box<[Clause]>) -> String {
        let (clauses, key) = {
            let key = format!("p cnf {} {}\n", num_vars, clauses.len());
            let clauses = clauses.iter().map(|clause| {
                let cmap = clause.lits().iter().map(|lit| {
                    let sign = String::from(
                        if lit.sign() == Sign::Neg { "-" }  else { "" });
                    format!("{}{}", sign, lit.var().to_u64().to_string())
                });
                let cvec: Vec<String> = cmap.collect();
                let cstr = cvec.join(" ");
                format!("{} 0", cstr)
            });
            let cvec: Vec<String> = clauses.collect();
            let cstr = cvec.join("\n");
            (cstr, key)
        };
        format!("{}{}\n", key, clauses)
    }

    /// Creates a SAT or CNF instance, converting it into a String
    /// `comments` is a list of comments which are inserted into the
    /// beginning of the resulting String.
    pub fn serialize(&self, comments: &Vec<String>) -> String {
        let comments: Vec<String> = comments.iter()
                .map(|x| format!("c {}", x))
                .collect();
        let comments: String = comments.join("\n");

        let body = self.to_string();
        format!("{}\n{}\n", comments, body)
    }
}

bitflags! {
    /// Possible extensions for `.sat` file SAT instances.
    pub struct Extensions: u32 {
        /// If no extensions are being used.
        const NONE = 0b00000000;
        /// If the XOR-Extension is being used to allow for `xor(..)` formulas.
        const XOR  = 0b00000001;
        /// If the EQ-Extension is being used to allow for `=(..)` formulas.
        const EQ   = 0b00000010;
    }
}

impl ToString for Extensions {
    fn to_string(&self) -> String {
        let eqxor = Extensions::EQ | Extensions::XOR;
        if *self == eqxor {
            String::from("satex")
        } else {
            String::from(match *self {
                Extensions::NONE => "sat",
                Extensions::XOR  => "satx",
                Extensions::EQ   => "sate",
                _ => "Illegal extension"
            })
        }
    }
}
