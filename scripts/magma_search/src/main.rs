use clap::Parser;
use db::{Database, Equation, Implication, NonImplication, Proof, Term};
use image::RgbImage;
use ratatui::{
    crossterm::event::{self, KeyCode, KeyEventKind},
    widgets::Paragraph,
    DefaultTerminal,
};
use regex::Regex;
use searcher::ReflexiveSearcher;
use searcher::Searcher;
use std::{sync::RwLock, time::Duration};

// ===========================================================================

pub mod db;
pub mod searcher;

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
            draw(terminal, message)?;
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

    // generate image
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
                        use Implication::*;
                        use NonImplication::*;
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

    // done
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
