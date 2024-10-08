use regex::Regex;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::{collections::BTreeMap, fmt::Display, sync::LazyLock};

// ===========================================================================

#[derive(Debug, Serialize, Deserialize, Clone)]
#[serde(untagged)]
pub enum Term {
    Var(char),
    BinOp(Box<Term>, Box<Term>),
}

impl Default for Term {
    fn default() -> Self {
        Term::Var('x')
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(var) => write!(f, "{}", var),
            Term::BinOp(lhs, rhs) => write!(f, "({lhs} ∘ {rhs})"),
        }
    }
}

static RE_VAR: LazyLock<Regex> = LazyLock::new(|| Regex::new(r#"\w"#).unwrap());

impl Term {
    pub fn parse(s: &str) -> Result<Self, String> {
        if s.len() == 1 {
            return Ok(Term::Var(s.chars().next().unwrap()));
        }
        // modify the string to be parseable
        let s1 = s.replace("∘", ",");
        let s2 = RE_VAR.replace_all(&s1, "'$0'");
        let s3 = format!("({s2})");
        // parse the string
        ron::de::from_str::<Term>(&s3)
            .map_err(|e| format!("Failed to parse term: <{s}> <{s1}> <{s2}> <{s3}> {e}"))
    }

    pub fn free_vars(&self) -> BTreeSet<char> {
        match self {
            Term::Var(var) => {
                let mut vars = BTreeSet::new();
                vars.insert(*var);
                vars
            }
            Term::BinOp(lhs, rhs) => {
                let mut vars = lhs.free_vars();
                vars.extend(rhs.free_vars());
                vars
            }
        }
    }

    pub fn evaluate(&self, model: &Model, vars: &BTreeMap<char, u8>) -> u8 {
        match self {
            Term::Var(var) => *vars.get(var).unwrap(),
            Term::BinOp(lhs, rhs) => {
                let lhs_val = lhs.evaluate(model, vars);
                let rhs_val = rhs.evaluate(model, vars);
                model.magma[lhs_val as usize][rhs_val as usize]
            }
        }
    }
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct Equation(pub Term, pub Term);

impl Equation {
    pub fn free_vars(&self) -> BTreeSet<char> {
        let mut vars = self.0.free_vars();
        vars.extend(self.1.free_vars());
        vars
    }

    pub fn evaluate(&self, model: &Model, vars: &BTreeMap<char, u8>) -> bool {
        let lhs_val = self.0.evaluate(model, vars);
        let rhs_val = self.1.evaluate(model, vars);
        lhs_val == rhs_val
    }

    pub fn valid(&self, model: &Model) -> bool {
        let free_vars = self.free_vars();
        let size = model.magma.len();
        for i in 0..(free_vars.len().pow(size as u32)) {
            let mut vars = BTreeMap::new();
            let mut i = i;
            for var in free_vars.iter() {
                vars.insert(*var, (i % size as usize) as u8);
                i /= size as usize;
            }
            if !self.evaluate(model, &vars) {
                return false;
            }
        }
        true
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub enum Proof {
    Implication(Implication),
    NonImplication(NonImplication),
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub enum Implication {
    /// an egg Explanation
    Explanation,
    /// transitivity from A --> B and B --> C
    Transitivity(usize, usize, usize),
    /// reflexivity from A --> A
    Reflexivity,
    /// an external Lean proof
    Lean(String),
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub enum NonImplication {
    /// a counter-example model
    Model(Model),
    /// an external Lean proof
    Lean(String),
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Model {
    pub magma: Vec<Vec<u8>>,
}

impl Model {
    pub fn rand(size: u8) -> Self {
        let mut magma = vec![vec![0; size as usize]; size as usize];
        for i in 0..size {
            for j in 0..size {
                magma[i as usize][j as usize] = rand::random::<u8>() % size;
            }
        }
        Self { magma }
    }
}

// ===========================================================================

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct Database {
    #[serde(default)]
    pub equations: BTreeMap<usize, Equation>,
    #[serde(default)]
    pub proofs: BTreeMap<usize, BTreeMap<usize, Vec<Proof>>>,
}
