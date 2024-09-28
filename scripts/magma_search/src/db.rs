use regex::Regex;
use serde::{Deserialize, Serialize};
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
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct Equation(pub Term, pub Term);

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
    magma: Vec<Vec<usize>>,
}

pub fn interpret(_equation: &Equation, _magma: &Model) -> bool {
    todo!()
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct Database {
    #[serde(default)]
    pub equations: BTreeMap<usize, Equation>,
    #[serde(default)]
    pub proofs: BTreeMap<usize, BTreeMap<usize, Vec<Proof>>>,
}
