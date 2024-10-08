use std::{collections::BTreeMap, sync::RwLock};

use crate::database::{Database, Equation, Implication, Model, NonImplication, Proof};

// ===========================================================================

pub trait Searcher {
    fn init(&mut self, db: &RwLock<Database>) -> Result<(), String>;
    fn step(&mut self, db: &RwLock<Database>) -> Result<usize, String>;
}

// ===========================================================================

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

// ===========================================================================

pub struct ModelSearcher {
    eqs: BTreeMap<usize, Equation>,
}

impl Default for ModelSearcher {
    fn default() -> Self {
        Self::new()
    }
}

impl ModelSearcher {
    pub fn new() -> Self {
        Self {
            eqs: Default::default(),
        }
    }
}

impl Searcher for ModelSearcher {
    fn init(&mut self, db: &RwLock<Database>) -> Result<(), String> {
        let read = db.read().map_err(|e| e.to_string())?;
        self.eqs = read.equations.clone();
        Ok(())
    }

    fn step(&mut self, db: &RwLock<Database>) -> Result<usize, String> {
        let size = 4;
        let model = Model::rand(size);

        let mut valid = Vec::new();
        let mut invalid = Vec::new();
        for (name, eq) in &self.eqs {
            if eq.valid(&model) {
                valid.push(*name);
            } else {
                invalid.push(*name);
            }
        }

        let mut new = BTreeMap::new();
        let read = db.read().map_err(|e| e.to_string())?;
        for name1 in valid.iter() {
            // news
            if let Some(proofs) = read.proofs.get(name1) {
                new.insert(
                    *name1,
                    invalid
                        .iter()
                        .filter(|name2| !proofs.contains_key(*name2))
                        .cloned()
                        .collect(),
                );
            } else {
                new.insert(*name1, invalid.clone());
            }
        }
        drop(read);

        if new.is_empty() {
            return Ok(0);
        }

        let found = new.len();

        let mut write = db.write().map_err(|e| e.to_string())?;
        for (name1, name2s) in new {
            let proofs = write.proofs.entry(name1).or_default();
            for name2 in name2s {
                let proof = Proof::NonImplication(NonImplication::Model(model.clone()));
                proofs.insert(name2, vec![proof]);
            }
        }

        Ok(found)
    }
}
