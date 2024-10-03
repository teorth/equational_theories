use clap::{Parser, Subcommand};
use export::{AppHead, Expr, ExprId, Function, Fixity, Rule, RuleDirection};
use fxhash::FxHashMap;
use regex::Regex;
use ron::de::SpannedError;
use serde::Serialize;
use serde_derive::Deserialize;
use smallvec::SmallVec;
use tempfile::NamedTempFile;
use std::{
    borrow::Cow, collections::{BTreeMap, BTreeSet, HashSet}, fmt::Display, fs::{self, File}, io::{self, BufRead, BufReader, BufWriter, Read, Write}, iter, path::{Path, PathBuf}, str::FromStr, sync::{Barrier, LazyLock, Mutex, RwLock, RwLockReadGuard}, thread, time::Duration
};
use egg::{define_language, Analysis, Applier, EGraph, ENodeOrVar, Id, Language, Pattern, PatternAst, RecExpr, Rewrite, Runner, SearchMatches, Subst, Symbol, Var};
use anyhow::{anyhow, Result};
use nix::{sys::wait::WaitStatus, unistd::{fork, ForkResult}};
use nix::sys::wait::waitpid;

mod export;

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

define_language! {
    #[derive(Serialize, Deserialize)]
    enum TermLang {
        "∘" = BinOp([Id; 2]),
        Var(char),
    }
}

static RE_VAR: LazyLock<Regex> = LazyLock::new(|| Regex::new(r#"\w"#).unwrap());

impl Term {
    fn parse(s: &str) -> Result<Self, SpannedError> {
        if s.len() == 1 {
            return Ok(Term::Var(s.chars().next().unwrap()));
        }
        // modify the string to be parseable
        let s1 = s.replace("∘", ",").replace("*", ",");
        let s2 = RE_VAR.replace_all(&s1, "'$0'");
        let s3 = if s2.contains(',') {format!("({s2})")} else {s2.into_owned()};
        ron::de::from_str::<Term>(&s3)
    }
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct Equation([Term; 2]);

#[derive(Debug, Serialize, Deserialize, Clone)]
pub enum Implication {
    // an egg Explanation
    Explanation(String),
    LetExplanation(String),
    // transitivity from A --> B and B --> C
    //Transitivity(usize, usize, usize),
    // reflexivity from A --> A
    //Reflexivity,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub enum NonImplication {
    // a counter-example model
    FiniteModel(Vec<Vec<usize>>),
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub enum Proof {
    Implication(Implication),
    NonImplication(NonImplication),
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct Database {
    #[serde(default)]
    pub proven: BTreeSet<(usize, usize)>,
    #[serde(default)]
    pub attempted: BTreeMap<(usize, usize), u64>,
}

fn write_with(path: impl AsRef<Path>, f: impl FnOnce(BufWriter<&File>) -> Result<()>) -> Result<()> {
    let path = path.as_ref();
    let out = NamedTempFile::new_in(path.parent().unwrap_or(&Path::new(".")))?;
    f(BufWriter::new(out.as_file()))?;
    out.persist(path)?;
    Ok(())
}

fn write_with_zstd<P, F>(path: P, compression_level: i32, f: F) -> Result<()>
where
    P: AsRef<Path>,
    F: FnOnce(&mut BufWriter<zstd::Encoder<BufWriter<&File>>>) -> Result<()>,
{
    write_with(path, |file| {
        let encoder = zstd::Encoder::new(file, compression_level)?;
        let mut writer: BufWriter<zstd::Encoder<'_, BufWriter<&File>>> = BufWriter::new(encoder);

        f(&mut writer)?;

        // Ensure all data is written and compressed
        let encoder = writer.into_inner().map_err(|e| io::Error::new(io::ErrorKind::Other, e.to_string()))?;
        encoder.finish()?;

        Ok(())
    })
}

fn write_ron<T: Serialize>(path: impl AsRef<Path>, value: &T) -> Result<()> {
    write_with(path, |w| Ok(ron::ser::to_writer_pretty(w, value, Default::default())?))
}

fn read_with_zstd<P, T, F>(path: P, f: F) -> io::Result<T>
where
    P: AsRef<Path>,
    F: FnOnce(BufReader<zstd::Decoder<BufReader<File>>>) -> T,
{
    let reader = File::open(path)?;
    let reader = zstd::Decoder::new(reader)?;
    let reader = BufReader::new(reader);

    Ok(f(reader))
}

impl Database {
    fn write(&self, path: impl AsRef<Path>) -> Result<()> {
        write_ron(path, self)
    }
}

fn add_term_to_recexpr(expr: &mut RecExpr<TermLang>, term: &Term) -> Id {
    let node = match term {
        Term::Var(c) => TermLang::Var(*c),
        Term::BinOp(lhs, rhs) => {
            let lhs = add_term_to_recexpr(expr, lhs);
            let rhs = add_term_to_recexpr(expr, rhs);
            TermLang::BinOp([lhs, rhs])
        }
    };
    expr.add(node)
}

fn recexpr_from_term(term: &Term) -> RecExpr<TermLang> {
    let mut expr = RecExpr::default();
    add_term_to_recexpr(&mut expr, term);
    expr
}

fn add_term_to_pattern_ast<L: Language>(pat: &mut PatternAst<L>, term: &Term, mut f: impl FnMut(Id, Id) -> L) -> Id {
    fn inner<L: Language>(pat: &mut PatternAst<L>, term: &Term, f: &mut impl FnMut(Id, Id) -> L) -> Id {
        let node = match term {
            Term::Var(c) => ENodeOrVar::Var(Var::from_str(&String::from_iter(['?', *c])).unwrap()),
            Term::BinOp(lhs, rhs) => {
                let lhs = inner(pat, lhs, f);
                let rhs = inner(pat, rhs, f);
                ENodeOrVar::ENode(f(lhs, rhs))
            }
        };
        pat.add(node)
    }
    inner(pat, term, &mut f)
}

fn pattern_ast_termlang_from_term(term: &Term) -> PatternAst<TermLang> {
    let mut pat = PatternAst::default();
    add_term_to_pattern_ast(&mut pat, term, |lhs, rhs| TermLang::BinOp([lhs, rhs]));
    pat
}

fn pattern_ast_node_from_term(term: &Term) -> PatternAst<Expr> {
    let mut pat = PatternAst::default();
    let head = AppHead {symbol: Symbol::new("F"), fixity: Fixity::Prefix};
    add_term_to_pattern_ast(&mut pat, term, |lhs, rhs| Expr::App(head, [ExprId(lhs), ExprId(rhs)].into()));
    pat
}

fn recexprs_from_equation(eq: &Equation) -> [RecExpr<TermLang>; 2] {
    eq.0.each_ref().map(|x| recexpr_from_term(&x))
}

fn patterns_from_equation(eq: &Equation) -> [Pattern<TermLang>; 2] {
    eq.0.each_ref().map(|x| Pattern::new(pattern_ast_termlang_from_term(&x)))
}

struct PartiallyBoundApplier<P> {
    applier: P,
    vars: Vec<Var>,
    values: Vec<Id>,
}

fn multi_assign(subst: &mut Subst, mut vars: impl Iterator<Item = Var> + Clone, values: impl IntoIterator<Item = Id> + Clone, f: &mut impl FnMut(&mut Subst)) {
    match vars.next() {
        None => f(subst),
        Some(var) => for value in values.clone().into_iter() {
            subst.insert(var, value);
            multi_assign(subst, vars.clone(), values.clone(), f);
        }
    }
}

impl<P> PartiallyBoundApplier<P>
{
    fn augment_substs<'a, L: Language, A: Analysis<L>>(&self, egraph: &EGraph<L, A>, substs: impl Iterator<Item = &'a Subst>) -> Vec<Subst>
        where P: Applier<L, A>
    {
        let mut out = Vec::new();
        let mut values: SmallVec<[Id; 64]> = self.values.iter().copied().map(|x| egraph.find(x)).collect();
        values.sort();
        values.dedup();

        for subst in substs {
            multi_assign(&mut subst.clone(), self.vars.iter().copied(), values.iter().copied(), &mut |subst|
                out.push(subst.clone()));
            /*
            for assignment in self.vars.iter().map(|_| values.iter().copied()).multi_cartesian_product() {
                for (&var, value) in self.vars.iter().zip(assignment) {
                    subst.insert(var, value);
                }
            }
            */
        }
        out
    }
}

impl<L: Language, A: Analysis<L>, P: Applier<L, A>> Applier<L, A> for PartiallyBoundApplier<P>
{
    fn get_pattern_ast(&self) -> Option<&PatternAst<L>> {
        self.applier.get_pattern_ast()
    }

    fn apply_matches(
        &self,
        egraph: &mut EGraph<L, A>,
        matches: &[SearchMatches<L>],
        rule_name: Symbol,
    ) -> Vec<Id> {
        let matches: Vec<_> = matches.into_iter().map(|m| {
            let substs = self.augment_substs(egraph, m.substs.iter());
            SearchMatches {eclass: m.eclass, substs, ast: m.ast.clone()}
        }).collect();
        self.applier.apply_matches(egraph, &matches, rule_name)
    }

    fn apply_one(
        &self,
        egraph: &mut EGraph<L, A>,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<L>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        let substs = self.augment_substs(egraph, iter::once(subst));
        let matches = SearchMatches {eclass, substs, ast: searcher_ast.map(|x| Cow::Borrowed(x))};
        self.applier.apply_matches(egraph, &[matches], rule_name)
    }

    fn vars(&self) -> Vec<Var> {
        self.applier.vars().into_iter().filter(|var| !self.vars.contains(var)).collect()
    }
}


fn add_rules(rules: &mut Vec<Rewrite<TermLang, ()>>, goal_exprs: &[Id], name: &str, lhs: &Pattern<TermLang>, rhs: &Pattern<TermLang>) -> Result<()> {
    let lhs_vars: HashSet<_> = lhs.vars().into_iter().collect();
    let vars = rhs.vars().into_iter().filter(|x| !lhs_vars.contains(x)).collect();
    let values = goal_exprs.into_iter().copied().collect();
    let rhs = PartiallyBoundApplier {
        applier: rhs.clone(),
        vars,
        values
    };
    rules.push(Rewrite::new(name, lhs.clone(), rhs).map_err(|e| anyhow!(e))?);
    Ok(())
}

pub fn add_vars<L>(vars: &mut Vec<Var>, ast: &PatternAst<L>) {
    for n in ast.as_ref() {
        if let ENodeOrVar::Var(v) = n {
            if !vars.contains(v) {
                vars.push(*v)
            }
        }
    }
}

fn equation_vars(eq: &Equation) -> Vec<Var> {
    let [lhs, rhs] = eq.0.each_ref().map(|x| pattern_ast_termlang_from_term(&x));
    let mut vars = Vec::new();
    add_vars(&mut vars, &lhs);
    add_vars(&mut vars, &rhs);
    vars
}

fn add_equation_to_rules(rules: &mut FxHashMap<Symbol, Rule>, name: &str, eq: &Equation) {
    let [lhs, rhs] = eq.0.each_ref().map(|x| pattern_ast_node_from_term(&x));
    let name = Symbol::new(name);
    let mut vars = Vec::new();
    add_vars(&mut vars, &lhs);
    add_vars(&mut vars, &rhs);
    rules.insert(Symbol::new(format!("{}f", name)), Rule::new(lhs.clone(), rhs.clone(), name, vars.clone(), RuleDirection::Forward));
    rules.insert(Symbol::new(format!("{}b", name)), Rule::new(rhs, lhs, name, vars, RuleDirection::Backward));
}

fn derive_equation(h: &Equation, goal: &Equation, ms: u64, node_limit: usize, length_optimization: bool) -> Result<Option<egg::Explanation<TermLang>>> {
    let h = patterns_from_equation(h);
    let goal = recexprs_from_equation(goal);

    let runner = Runner::default()
        .with_explanations_enabled()
        .with_node_limit(node_limit)
        .with_time_limit(Duration::from_millis(ms))
        .with_expr(&goal[0])
        .with_expr(&goal[1]);

    let runner = if length_optimization {
        runner.with_explanation_length_optimization()
    } else {
        runner.without_explanation_length_optimization()
    };

    let goal_exprs: Vec<_> = runner.egraph.classes().map(|x| x.id).collect();

    let mut rules = Vec::new();
    add_rules(&mut rules, &goal_exprs, "hf", &h[0], &h[1])?;
    add_rules(&mut rules, &goal_exprs, "hb", &h[1], &h[0])?;

    let mut runner = runner.run(&rules);
    eprintln!("stop: {:?}", runner.stop_reason);

    let roots = [runner.roots[0], runner.roots[1]];
    let roots = roots.map(|x| runner.egraph.find(x));

    if roots[0] == roots[1] {
        eprintln!("explain now");
        Ok(Some(runner.explain_equivalence(&goal[0], &goal[1])))
    } else {
        Ok(None)
    }
}



fn read_equations(path: impl AsRef<Path>) -> Result<Vec<Equation>> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    let re = Regex::new(r#"\s*(?:--)?\s*equation (\d+)\s*:=\s*([^=]*)\s*=\s*([^=]*)"#).unwrap();

    let mut equations = Vec::new();
    for line in reader.lines() {
        let line = line?;
        if let Some(captures) = re.captures(&line) {
            let idx = captures.get(1).unwrap().as_str().parse::<usize>()?;
            let lhs = Term::parse(captures.get(2).unwrap().as_str())?;
            let rhs = Term::parse(captures.get(3).unwrap().as_str())?;
            let equation = Equation([lhs, rhs]);
            if idx >= equations.len() {
                equations.resize(idx + 1, Equation::default())
            }
            equations[idx] = equation;
        }
    }

    Ok(equations)
}

fn implication_regex() -> Regex {
    Regex::new(r#"^\D*(\d+)\D*(\d+)\D*$"#).unwrap()
}

fn read_implications(path: impl AsRef<Path>) -> Result<Vec<(usize, usize)>> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    let re = implication_regex();

    let mut implications = Vec::new();
    for line in reader.lines() {
        let line = line?;
        if let Some(captures) = re.captures(&line) {
            let h = captures.get(1).unwrap().as_str().parse::<usize>()?;
            let goal = captures.get(2).unwrap().as_str().parse::<usize>()?;
            implications.push((h, goal))
        }
    }

    Ok(implications)
}

fn write_proof(dir: impl AsRef<Path>, implication: (usize, usize), proof: &Proof) -> Result<()> {
    let (ext, s) = match proof {
        Proof::Implication(Implication::LetExplanation(s)) => ("let", s),
        Proof::Implication(Implication::Explanation(s)) => ("flat", s),
        Proof::NonImplication(NonImplication::FiniteModel(_f)) => ("finite", &String::new()) // TODO
    };
    let path = dir.as_ref().join(format!("{}_{}.{}.zst", implication.0, implication.1, ext));
    write_with_zstd(path, 0, |w| Ok(w.write_all(s.as_bytes())?))
}

fn try_read_proof<T>(dir: impl AsRef<Path>, implication: (usize, usize), ext: &str, f: impl FnOnce(BufReader<zstd::Decoder<BufReader<File>>>) -> T) -> Result<Option<T>> {
    let path = dir.as_ref().join(format!("{}_{}.{}.zst", implication.0, implication.1, ext));
    match read_with_zstd(path, f) {
        Ok(x) => {Ok(Some(x))},
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => return Err(e)?
    }
}

pub struct SpaceSqueezer<R> {
    inner: R,
    last_was_whitespace: bool,
}

impl<R: Read> SpaceSqueezer<R> {
    pub fn new(inner: R) -> Self {
        SpaceSqueezer {
            inner,
            last_was_whitespace: false,
        }
    }

    fn is_whitespace(byte: u8) -> bool {
        byte == b' ' || byte == b'\t'
    }
}

impl<R: Read> Read for SpaceSqueezer<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        loop {
            let bytes_read = self.inner.read(buf)?;
            if bytes_read == 0 {
                return Ok(0);
            }

            let mut bytes_written = 0;
            for i in 0..bytes_read {
                let byte = buf[i];
                if Self::is_whitespace(byte) {
                    if !self.last_was_whitespace {
                        buf[bytes_written] = byte;
                        bytes_written += 1;
                        self.last_was_whitespace = true;
                    }
                } else {
                    buf[bytes_written] = byte;
                    bytes_written += 1;
                    self.last_was_whitespace = false;
                }
            }

            if bytes_written > 0 {
                return Ok(bytes_written);
            }
        }
    }
}


fn read_proof(dir: impl AsRef<Path>, implication: (usize, usize)) -> Result<Option<Proof>> {
    if let Some(proof) = try_read_proof(dir, implication, "let", |reader| {
        // TODO: this is horribly inefficient, switch to a decent sexp crate that actually has basic features like incremental parsing

        // squeeze spaces so we are much less likely to OOM when reading pretty printed sexps
        let mut reader = BufReader::new(SpaceSqueezer::new(reader));

        let mut buf = Vec::new();
        reader.read_to_end(&mut buf)?;
        let str = String::from_utf8(buf)?;
        Ok::<_, anyhow::Error>(Proof::Implication(Implication::LetExplanation(str)))
    })? {
        return Ok(Some(proof?))
    }
    Ok(None)
}

fn with_stack_size<T: Send>(stack_size: usize, f: impl FnOnce() -> T + Send) -> T {
    thread::scope(|scope| {
        let worker = thread::Builder::new().stack_size(stack_size).spawn_scoped(scope, move || {
            f()
        }).unwrap();

        worker.join().unwrap()
    })
}

struct SubprocessSpawner<'a, 'b> {
    mt_lock: &'a RwLock<()>,
    mt_guard: &'b mut Option<RwLockReadGuard<'a, ()>>
}

impl<'a, 'b> SubprocessSpawner<'a, 'b> {
    fn in_subprocess(&mut self, f: impl FnOnce() -> i32) -> Result<i32> {
        *self.mt_guard = None;
        let mt_write_guard = self.mt_lock.write().unwrap();
        let status = match unsafe { fork() }? {
            ForkResult::Parent { child } => {
                drop(mt_write_guard);
                waitpid(child, None)?
            }
            ForkResult::Child => {
                drop(mt_write_guard);
                let res = f();
                unsafe { libc::_exit(res) };
            }
        };
        *self.mt_guard = Some(self.mt_lock.read().unwrap());

        match status {
            WaitStatus::Exited(_, ret) => Ok(ret),
            status => Err(anyhow!("fork child terminated due to {:?}", status))
        }
    }

    fn in_subprocess_with_stack_size(&mut self, stack_size: usize, f: impl FnOnce() -> i32 + Send) -> Result<i32> {
        self.in_subprocess(|| {
            with_stack_size(stack_size, f)
        })
    }
}

fn in_parallel<E: Send>(parallelism: usize, f: impl Fn(usize) -> Result<(), E> + Sync) -> Result<(), E> {
    let f = &f;
    thread::scope(|scope| {
        let handles = (0..parallelism).map(|i| {
            scope.spawn(move || f(i))
        }).collect::<Vec<_>>();

        for handle in handles {
            handle.join().unwrap()?;
        }
        Ok(())
    })
}

// technically forking in a multithreaded program is UB,
// but we use barrier and mt_lock to ensure that all other threads are also inside in_subprocess, either waiting for the write lock or in waitpid()
// so it should be fine for any reasonable libc implementation

// alternatively we could fork a single process at startup and then communicate with it to have it spawn more processes
// or spawn processes to parallelize and use IPC or file system locks to get work items

// we have to use a subprocess because this can stack overflow or get OOM killed
fn process_in_parallel_with_subprocess_spawner<E: Send, I: IntoIterator<Item: Send>>(parallelism: usize, items: I, f: impl Fn(&mut SubprocessSpawner, I::Item) -> Result<(), E> + Sync) -> Result<(), E> {
    let mut items: Vec<_> = items.into_iter().collect();
    items.reverse();
    let items = Mutex::new(items);

    let mt_lock = &RwLock::new(());
    let barrier = Barrier::new(parallelism);

    in_parallel(parallelism, |_| {
        // make sure we don't fork while a thread is being spawned
        barrier.wait();
        let mut mt_guard = Some(mt_lock.read().unwrap());
        let mut spawner = SubprocessSpawner {mt_lock, mt_guard: &mut mt_guard};
        loop {
            let item = items.lock().unwrap().pop();
            if let Some(item) = item {
                f(&mut spawner, item)?
            } else {
                break
            }
        }
        Ok::<_, E>(())
    })
}

#[derive(Parser, Debug)]
struct Args {
    /// Database file path
    #[clap(long)]
    db: PathBuf,
    /// Load equations from Lean file
    #[clap(long)]
    equations: PathBuf,
    /// Load implications to search for from file
    #[clap(long)]
    implications: PathBuf,
    /// Directory to write proofs in
    #[clap(long)]
    proofs: PathBuf,
    /// Number of threads to spawn
    #[clap(long)]
    parallelism: Option<usize>,
    /// Stack size in bytes
    #[clap(long, default_value = "268435456")]
    stack_size: usize
}

struct App {
    args: Args,
    db: Database,
    equations: Vec<Equation>,
    implications: Vec<(usize, usize)>,
    parallelism: usize
}

impl App {
    fn new(args: Args) -> Result<Self> {
        std::fs::create_dir_all(&args.proofs)?;

        let db: Database = match File::open(&args.db) {
            Ok(db) => ron::de::from_reader(BufReader::new(db))?,
            Err(e) => if e.kind() == io::ErrorKind::NotFound {
                Default::default()
            } else {
                return Err(e)?
            }
        };

        let equations = read_equations(&args.equations)?;
        let implications = read_implications(&args.implications)?;
        let parallelism = args.parallelism.or_else(|| std::thread::available_parallelism().map(|x| x.into()).ok()).unwrap_or(1);

        Ok(App {args, db, equations, implications, parallelism})
    }
}

#[derive(Parser, Debug)]
struct ForgetArgs {
    /// Forget that we proved or attempted the implications in this file
    forget: PathBuf
}

impl App {
    fn forget(mut self, args: ForgetArgs) -> Result<()> {
        let implications = read_implications(&args.forget)?;
        for implication in implications {
            self.db.attempted.remove(&implication);
            self.db.proven.remove(&implication);
        }

        self.db.write(&self.args.db)?;
        Ok(())
    }
}

#[derive(Parser, Debug)]
struct SearchArgs {
    /// Time limit in milliseconds
    #[clap(long)]
    ms: u64,
    /// Node limit
    #[clap(long, default_value = "16777216")]
    node_limit: usize
}

impl App {
    fn search(self, args: SearchArgs) -> Result<()> {
        let implications: Vec<_> = self.implications.into_iter().filter(|x| !self.db.proven.contains(x) && self.db.attempted.get(x).filter(|&&x| x >= args.ms).is_none()).collect();
        let db = Mutex::new(self.db);

        process_in_parallel_with_subprocess_spawner(self.parallelism,implications, |spawner, item| {
            let (h, goal) = item;
            eprintln!("{} => {}", h, goal);
            let mut proven = false;
            for length_optimization in [true, false] {
                let ret = spawner.in_subprocess_with_stack_size(self.args.stack_size, || {
                    let res = (|| {
                        let res = derive_equation(&self.equations[h], &self.equations[goal], args.ms, args.node_limit, length_optimization)?;
                        if let Some(explanation) = res {
                            let str = explanation.get_string_with_let();
                            eprintln!("{} => {}: proven with len {}", h, goal, str.len());
                            write_proof(&self.args.proofs, (h, goal), &Proof::Implication(Implication::LetExplanation(str)))?;
                            Ok::<_, anyhow::Error>(0)
                        } else {
                            Ok(1)
                        }
                    })();

                    match res {
                        Ok(x) => x,
                        Err(e) => {
                            eprintln!("{}", e);
                            3
                        }
                    }
                });

                match ret {
                    Ok(0) => {proven = true; break},
                    Ok(1) => {break}
                    _ => {}
                }
            }
            let mut db = db.lock().unwrap();
            if proven {
                db.proven.insert((h, goal));
            } else {
                db.attempted.insert((h, goal), args.ms);
            }
            db.write(&self.args.db)?;
            Ok(())
        })
    }
}


#[derive(Parser, Debug)]
struct ExportArgs {
}

impl App {
    fn export(self, _args: ExportArgs) -> Result<()> {
        let implications: Vec<_> = self.implications.into_iter().filter(|x| self.db.proven.contains(x)).collect();

        process_in_parallel_with_subprocess_spawner(self.parallelism,implications, |spawner, implication| {
            spawner.in_subprocess_with_stack_size(self.args.stack_size, || {
                let res = (|| {
                    let (h, goal) = implication;
                    eprintln!("{} => {}", h, goal);
                    let proof = read_proof(&self.args.proofs, implication)?;
                    if let Some(proof) = proof {
                        match proof {
                            Proof::Implication(Implication::LetExplanation(str)) => {
                                let sexp = symbolic_expressions::parser::parse_str(&str)?;
                                drop(str);

                                let mut rules = FxHashMap::default();
                                add_equation_to_rules(&mut rules, "h", &self.equations[h]);

                                let mut functions = FxHashMap::default();
                                functions.insert(Symbol::new("∘"), Function {head: AppHead {symbol: Symbol::new("F"), fixity: Fixity::Prefix}, congr: Symbol::new("C")});

                                let lean = export::convert_explanation_to_lean_proof(&sexp, &rules, &functions)?;

                                let path = self.args.proofs.join(format!("{}_{}.lean.zst", implication.0, implication.1));
                                write_with_zstd(path, 0, |out| Ok(out.write_all(lean.as_bytes())?))?;
                            },
                            _ => {}
                        }
                    }
                    Ok::<_, anyhow::Error>(())
                })();
                match res {
                    Ok(_) => 0,
                    Err(e) => {
                        eprintln!("{}", e);
                        1
                    }
                }
            })?;
            Ok(())
        })
    }
}

#[derive(Parser, Debug)]
struct AssembleArgs {
    /// Directory to write the output files to
    output: PathBuf
}

struct OutputFile {
    writer: BufWriter<NamedTempFile>,
    path: PathBuf,
    lines: u64
}

impl OutputFile {
    fn new(output: impl AsRef<Path>, name: impl AsRef<Path>) -> Result<OutputFile> {
        fs::create_dir_all(&output)?;
        let output = output.as_ref();
        let temp = NamedTempFile::new_in(output)?;
        let writer = BufWriter::new(temp);
        let path = output.join(name);
        let lines = 0;
        Ok(Self {writer, path, lines})
    }

    fn close(self) -> Result<()> {
        let temp = self.writer.into_inner()?;
        temp.persist(self.path)?;
        Ok(())
    }

    fn append(&mut self, s: &str, lines: u64) -> Result<()> {
        self.writer.write_all(s.as_bytes())?;
        self.lines += lines;
        Ok(())
    }

    fn lines(&self) -> u64 {
        self.lines
    }
}

impl App {
    fn assemble(self, args: AssembleArgs) -> Result<()> {
        let re = implication_regex();
        let mut proofs = Vec::new();

        for entry in fs::read_dir(&self.args.proofs)? {
            let entry = entry?;
            let os_name = entry.file_name();
            if let Some(name) = os_name.as_os_str().to_str() {
                if name.ends_with(".lean.zst") {
                    if let Some(captures) = re.captures(&name) {
                        let h = captures.get(1).unwrap().as_str().parse::<usize>()?;
                        let goal = captures.get(2).unwrap().as_str().parse::<usize>()?;
                        let size = entry.metadata()?.len();
                        proofs.push((size, (h, goal), os_name));
                    }
                }
            }
        }

        proofs.sort();

        let header =
r#"import equational_theories.AllEquations
import equational_theories.Magma

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ∘ c = b ∘ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

"#;
        let header_lines = header.chars().filter(|x| *x == '\n').count() as u64;

        let big_header = "set_option maxRecDepth 999999\n\n";
        let big_header_lines = big_header.chars().filter(|x| *x == '\n').count() as u64;

        let mut cur_small: Option<OutputFile> = None;
        let mut next_small_idx = 0;

        let small_theorem_threshold = 100u64;
        let small_file_threshold = 1000u64;

        let output_small = args.output.join("small");
        let output_large = args.output.join("Large");
        let mut large_files = Vec::new();

        for (_size, (h, goal), os_name) in proofs {
            let proof = read_with_zstd(self.args.proofs.join(os_name), |mut reader| {
                let mut str = String::new();
                reader.read_to_string(&mut str)?;
                Ok::<_, anyhow::Error>(str)
            })??;

            let proof = (String::from("\n") + &proof).replace("\n", "\n  ");
            let proof = proof.replace("F", "M"); // we used to use F instead of M

            let goal_vars = equation_vars(&self.equations[goal]);
            let goal_vars = goal_vars.into_iter().map(|x| String::from(&x.to_string()[1..]));
            let goal_vars = goal_vars.collect::<Vec<_>>().join(" ");

            let proof = format!("@[equational_result]\ntheorem Equation{h}_implies_Equation{goal} (G: Type _) [Magma G] (h: Equation{h} G) : Equation{goal} G := fun {goal_vars} =>{proof}\n\n");

            let lines = proof.chars().filter(|x| *x == '\n').count() as u64;

            if lines <= small_theorem_threshold {
                let mut close_small = false;

                if let Some(out) = &cur_small {
                    if out.lines() + lines >= small_file_threshold {
                        close_small = true
                    }
                }

                if close_small {
                    if let Some(out) = cur_small {
                        out.close()?;
                        cur_small = None;
                    }
                }

                if cur_small.is_none() {
                    let out_name = format!("MagmaEgg_small{:02}.lean", next_small_idx);
                    next_small_idx += 1;

                    let mut out = OutputFile::new(&output_small, &out_name)?;
                    out.append(header, header_lines)?;
                    cur_small = Some(out);
                }

                if let Some(out) = &mut cur_small {
                    out.append(&proof, lines)?;
                }
            } else {
                let out_name = format!("MagmaEgg_{}_{}", h, goal);
                let mut out = OutputFile::new(&output_large, &format!("{}.lean", out_name))?;
                large_files.push(out_name);
                out.append(header, header_lines)?;
                out.append(big_header, big_header_lines)?;
                out.append(&proof, lines)?;
                out.close()?
            }
        }

        if let Some(out) = cur_small {
            out.close()?;
        }

        let mut out = OutputFile::new(&args.output, "small.lean")?;
        for i in 0..next_small_idx {
            out.append(&format!("import equational_theories.Generated.MagmaEgg.small.MagmaEgg_small{:02}\n", i), 1)?;
        }
        out.close()?;

        let mut out = OutputFile::new(&args.output, "Large.lean")?;
        for large_file in large_files {
            out.append(&format!("import equational_theories.Generated.MagmaEgg.Large.{}\n", large_file), 1)?;
        }
        out.close()?;

        Ok(())
    }
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
/// Search for proofs of implication/non-implication in magmas and export them to Lean
struct Cli {
    #[command(subcommand)]
    command: Commands,

    #[command(flatten)]
    args: Args,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Search for proofs of implication/non-implication in magmas
    Search(SearchArgs),
    /// Export results to Lean source code
    Export(ExportArgs),
    /// Assemble Lean code to create mergeable files
    Assemble(AssembleArgs),
    /// Forget that some implications were attempted or proven
    Forget(ForgetArgs),
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let app = App::new(cli.args)?;

    match cli.command {
        Commands::Search(args) => app.search(args),
        Commands::Export(args) => app.export(args),
        Commands::Forget(args) => app.forget(args),
        Commands::Assemble(args) => app.assemble(args)
    }
}
