use std::sync::RwLock;

use crate::db::{Database, Implication, Proof};

// ===========================================================================

pub trait Searcher {
    fn init(&mut self, db: &RwLock<Database>) -> Result<(), String>;
    fn step(&mut self, db: &RwLock<Database>) -> Result<usize, String>;
}

/// Dummy example Searcher
pub struct ReflexiveSearcher {
    eqs: Vec<usize>,
}

impl Default for ReflexiveSearcher {
    fn default() -> Self {
        Self::new()
    }
}

impl ReflexiveSearcher {
    pub fn new() -> Self {
        Self { eqs: vec![] }
    }
}

impl Searcher for ReflexiveSearcher {
    fn init(&mut self, db: &RwLock<Database>) -> Result<(), String> {
        let read = db.read().map_err(|e| e.to_string())?;
        self.eqs = read.equations.keys().cloned().collect();
        Ok(())
    }

    fn step(&mut self, db: &RwLock<Database>) -> Result<usize, String> {
        if let Some(eq) = self.eqs.pop() {
            let mut write = db.write().map_err(|e| e.to_string())?;
            let proofs = write.proofs.entry(eq).or_default().entry(eq).or_default();
            if proofs.is_empty() {
                proofs.push(Proof::Implication(Implication::Reflexivity));
                return Ok(1);
            }
        }
        Ok(0)
    }
}
