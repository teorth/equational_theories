use clap::Parser;
use image::RgbImage;
use ratatui::{
    crossterm::event::{self, KeyCode, KeyEventKind},
    widgets::Paragraph,
    DefaultTerminal,
};
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeMap,
    fmt::Display,
    sync::{LazyLock, RwLock},
    time::Duration,
};

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
    fn parse(s: &str) -> Result<Self, String> {
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
pub struct Equation(Term, Term);

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
use Implication::*;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub enum NonImplication {
    /// a counter-example model
    Model(Model),
    /// an external Lean proof
    Lean(String),
}
use NonImplication::*;

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

// ===========================================================================

trait Searcher {
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

// ===========================================================================

fn run(args: &Args, mut terminal: DefaultTerminal) -> Result<(), String> {
    // utils
    let mut message = String::new();
    let draw = |terminal: &mut DefaultTerminal, msg: &str| -> Result<(), String> {
        terminal
            .draw(|frame| {
                let greeting = Paragraph::new(msg);
                frame.render_widget(greeting, frame.area());
            })
            .map_err(|e| e.to_string())?;
        Ok(())
    };
    let wait = |terminal: &mut DefaultTerminal, message: &mut String| -> Result<(), String> {
        if args.debug {
            message.push_str("Press any key to continue...\n");
            draw(terminal, &message)?;
            event::read().map_err(|e| e.to_string())?;
        }
        Ok(())
    };

    // load db
    message.clear();
    let mut db = if args.wipe {
        message.push_str("Wiping DB...\n");
        draw(&mut terminal, &message)?;
        Database::default()
    } else {
        message.push_str(&format!("Reading DB from {}...\n", args.db));
        draw(&mut terminal, &message)?;
        let db_content = std::fs::read_to_string(args.db.as_str()).map_err(|e| e.to_string())?;
        message.push_str("Deserializing DB...\n");
        draw(&mut terminal, &message)?;
        ron::de::from_str::<Database>(&db_content).map_err(|e| e.to_string())?
    };

    // load equations
    if let Some(equations) = &args.equations {
        message.push_str(&format!("Reading equations from {}...\n", equations));
        draw(&mut terminal, &message)?;
        let equations_content =
            std::fs::read_to_string(equations.as_str()).map_err(|e| e.to_string())?;
        let re = Regex::new(r#"equation (\d+) := (.*) = (.*)"#).map_err(|e| e.to_string())?;
        for captures in re.captures_iter(&equations_content) {
            message.push_str(&format!("{:?}\n", captures.get(0).unwrap()));
            let ind = captures
                .get(1)
                .unwrap()
                .as_str()
                .parse::<usize>()
                .map_err(|e| e.to_string())?;
            let lhs = Term::parse(captures.get(2).unwrap().as_str())?;
            let rhs = Term::parse(captures.get(3).unwrap().as_str())?;
            let equation = Equation(lhs, rhs);
            db.equations.insert(ind, equation);
        }
        draw(&mut terminal, &message)?;
    }

    wait(&mut terminal, &mut message)?;

    // search
    let mut steps = 0;
    let mut found_run = 0;
    let mut found_total = db.proofs.values().map(|ps| ps.len()).sum::<usize>();
    let found_goal = db.equations.len() * db.equations.len();
    let db = RwLock::new(db);
    let mut searcher = ReflexiveSearcher::new();
    searcher.init(&db)?;
    loop {
        steps += 1;
        let mut message = String::new();
        message.push_str("Searching... (press 'q' to quit)\n\n");

        let mut found_step = 0;
        found_step += searcher.step(&db)?;
        found_run += found_step;
        found_total += found_step;

        message.push_str("Stats:\n");
        message.push_str(&format!("- Steps: {steps}\n"));
        message.push_str(&format!("- Found this step: {found_step}\n"));
        message.push_str(&format!("- Found this run: {found_run}\n"));
        message.push_str(&format!("- Found total: {found_total}\n"));
        message.push_str(&format!("- Goal: {found_goal}\n"));
        message.push_str(&format!(
            "- Progress: {:.10}%\n",
            100.0 * found_total as f64 / found_goal as f64
        ));
        draw(&mut terminal, &message)?;

        if event::poll(Duration::from_millis(0)).map_err(|e| e.to_string())? {
            if let event::Event::Key(key) = event::read().map_err(|e| e.to_string())? {
                if key.kind == KeyEventKind::Press && key.code == KeyCode::Char('q') {
                    break;
                }
            }
        }
    }

    message.clear();

    if let Some(image) = &args.image {
        message.push_str(&format!("Generating image {image}...\n"));
        draw(&mut terminal, &message)?;
        let db = &*db.read().map_err(|e| e.to_string())?;

        let dim = db.equations.len() as u32;
        let mut img = RgbImage::new(dim, dim);
        for (i, eq1) in db.equations.keys().enumerate() {
            if let Some(proofs) = db.proofs.get(eq1) {
                for (j, eq2) in db.equations.keys().enumerate() {
                    if let Some(proofs) = proofs.get(eq2) {
                        let color = match proofs.first() {
                            Some(Proof::Implication(Explanation)) => [0, 255, 0],
                            Some(Proof::Implication(Reflexivity)) => [255, 255, 255],
                            Some(Proof::Implication(Transitivity(..))) => [0, 255, 255],
                            Some(Proof::Implication(Implication::Lean(_))) => [0, 255, 128],
                            Some(Proof::NonImplication(Model(_))) => [255, 0, 0],
                            Some(Proof::NonImplication(NonImplication::Lean(_))) => [255, 0, 128],
                            None => [0, 0, 0],
                        };
                        img.get_pixel_mut(i as u32, j as u32).0 = color;
                    }
                }
            }
        }
        img.save(image).map_err(|e| e.to_string())?;
    }

    // save db
    message.push_str("Serializing DB...\n");
    draw(&mut terminal, &message)?;
    let db = &*db.read().map_err(|e| e.to_string())?;
    let db_content =
        ron::ser::to_string_pretty(db, Default::default()).map_err(|e| e.to_string())?;
    message.push_str(&format!("Writing DB to {}...\n", args.db));
    draw(&mut terminal, &message)?;
    std::fs::write(args.db.as_str(), db_content).map_err(|e| e.to_string())?;

    wait(&mut terminal, &mut message)?;

    Ok(())
}

// ===========================================================================

/// Search for proofs of implication/non-implication in magmas
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// The name to say hello to
    #[clap(long, default_value = "db.ron")]
    db: String,
    /// Load equations from Lean file
    #[clap(long)]
    equations: Option<String>,
    /// Wipe the database before starting
    #[clap(long)]
    wipe: bool,
    /// Debug mode
    #[clap(long)]
    debug: bool,
    /// Generate an image from the database
    #[clap(long)]
    image: Option<String>,
}

fn main() -> Result<(), String> {
    let args = Args::parse();

    let mut terminal = ratatui::init();
    terminal.clear().map_err(|e| e.to_string())?;
    let app_result = run(&args, terminal);
    ratatui::restore();
    app_result
}
