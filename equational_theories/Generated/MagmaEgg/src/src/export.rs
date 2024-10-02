use bytemuck::TransparentWrapper;
use bytemuck_derive::TransparentWrapper;
use egg::{AstSize, EGraph, ENodeOrVar, Extractor, Id, Language, Pattern, PatternAst, RecExpr, Searcher, Subst, Symbol, Var};
use fxhash::FxHashMap;
use anyhow::{anyhow, bail, Context as _, Result};
use symbolic_expressions::Sexp;
use std::{fmt::{Display, Write}, mem};

#[derive(Clone, Debug, Copy, PartialOrd, Ord, PartialEq, Eq, Hash, TransparentWrapper)]
#[repr(transparent)]
pub struct ExprId(pub Id);

#[derive(Clone, Debug, Copy, PartialOrd, Ord, PartialEq, Eq, Hash, TransparentWrapper)]
#[repr(transparent)]
struct ProofId(pub Id);

#[derive(Clone, Debug, Copy, PartialOrd, Ord, PartialEq, Eq, Hash, TransparentWrapper)]
#[repr(transparent)]
pub struct InfoId(pub Id);

#[derive(Clone, Debug, Copy, PartialOrd, Ord, PartialEq, Eq, Hash, TransparentWrapper)]
#[repr(transparent)]
pub struct InfoOrExprId(pub Id);

impl From<InfoId> for InfoOrExprId {
    fn from(value: InfoId) -> Self {
        Self(value.0)
    }
}

impl From<ExprId> for InfoOrExprId {
    fn from(value: ExprId) -> Self {
        Self(value.0)
    }
}

#[derive(Clone, Debug, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum EnumInfoOrExprId {
    Info(InfoId),
    Expr(ExprId)
}

impl From<InfoId> for EnumInfoOrExprId {
    fn from(value: InfoId) -> Self {
        Self::Info(value)
    }
}

impl From<ExprId> for EnumInfoOrExprId {
    fn from(value: ExprId) -> Self {
        Self::Expr(value)
    }
}

impl From<EnumInfoOrExprId> for InfoOrExprId {
    fn from(value: EnumInfoOrExprId) -> Self {
        match value {
            EnumInfoOrExprId::Expr(id) => id.into(),
            EnumInfoOrExprId::Info(id) => id.into(),
        }
    }
}


#[derive(Clone, Debug, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Fixity {
    #[allow(dead_code)]
    Prefix,
    Infix
}

#[derive(Clone, Debug, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct AppHead {
    pub symbol: Symbol,
    pub fixity: Fixity
}

#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Expr {
    Var(Symbol),
    App(AppHead, Vec<ExprId>),
}

impl Language for Expr {
    fn matches(&self, other: &Self) -> bool {
        match (self, other) {
            (Expr::Var(sym1), Expr::Var(sym2)) => sym1 == sym2,
            (Expr::App(head1, _), Expr::App(head2, _)) => head1 == head2,
            _ => false,
        }
    }

    fn children(&self) -> &[Id] {
        match self {
            Expr::App(_, expr_ids) => ExprId::peel_slice(expr_ids.as_slice()),
            Expr::Var(_) => &[],
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            Expr::App(_, expr_ids) => ExprId::peel_slice_mut(expr_ids.as_mut_slice()),
            Expr::Var(_) => &mut [],
        }
    }
}

#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Info {
    Rewrite(RuleDirection, Symbol, ExprId),
    Explanation(Vec<InfoOrExprId>),
    App(Symbol, Vec<InfoOrExprId>)
}

impl Language for Info {
    fn matches(&self, other: &Self) -> bool {
        match (self, other) {
            (Info::Rewrite(dir1, sym1, _), Info::Rewrite(dir2, sym2, _)) => {
                dir1 == dir2 && sym1 == sym2
            },
            (Info::Explanation(_), Info::Explanation(_)) => true,
            (Info::App(head1, _), Info::App(head2, _)) => head1 == head2,
            _ => false,
        }
    }

    fn children(&self) -> &[Id] {
        match self {
            Info::Rewrite(_, _, expr_id) => std::slice::from_ref(&expr_id.0),
            Info::Explanation(ids) => InfoOrExprId::peel_slice(ids.as_slice()),
            Info::App(_, expr_ids) => InfoOrExprId::peel_slice(expr_ids.as_slice()),
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            Info::Rewrite(_, _, expr_id) => std::slice::from_mut(&mut expr_id.0),
            Info::Explanation(ids) => InfoOrExprId::peel_slice_mut(ids.as_mut_slice()),
            Info::App(_, expr_ids) => InfoOrExprId::peel_slice_mut(expr_ids.as_mut_slice()),
        }
    }
}


#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
enum Term {
    Hypothesis(Symbol, Vec<ExprId>),
    Reflexivity(ExprId),
    Symmetry(ProofId),
    Transitivity(Vec<ProofId>),
    Congruence(Symbol, Vec<ProofId>),
}

impl Language for Term {
    fn matches(&self, other: &Self) -> bool {
        match (self, other) {
            (Term::Hypothesis(sym1, args1), Term::Hypothesis(sym2, args2)) => {
                sym1 == sym2 && args1 == args2
            }
            (Term::Reflexivity(expr1), Term::Reflexivity(expr2)) => expr1 == expr2,
            (Term::Symmetry(_), Term::Symmetry(_)) => true,
            (Term::Transitivity(_), Term::Transitivity(_)) => true,
            (Term::Congruence(sym1, _), Term::Congruence(sym2, _)) => sym1 == sym2, // Ignore ProofId children
            _ => false,
        }
    }

    fn children(&self) -> &[Id] {
        match self {
            Term::Hypothesis(_, arg_ids) => ExprId::peel_slice(arg_ids.as_slice()),
            Term::Reflexivity(expr_id) => std::slice::from_ref(&expr_id.0),
            Term::Symmetry(proof_id) => std::slice::from_ref(&proof_id.0),
            Term::Transitivity(proof_ids) => ProofId::peel_slice(proof_ids.as_slice()),
            Term::Congruence(_, proof_ids) => ProofId::peel_slice(proof_ids.as_slice()),
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            Term::Hypothesis(_, arg_ids) => ExprId::peel_slice_mut(arg_ids.as_mut_slice()),
            Term::Reflexivity(expr_id) => std::slice::from_mut(&mut expr_id.0),
            Term::Symmetry(proof_id) => std::slice::from_mut(&mut proof_id.0),
            Term::Transitivity(proof_ids) => ProofId::peel_slice_mut(proof_ids.as_mut_slice()),
            Term::Congruence(_, proof_ids) => ProofId::peel_slice_mut(proof_ids.as_mut_slice()),
        }
    }
}

#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
enum ExprOrTermOrInfo {
    Expr(Expr),
    Term(Term),
    Info(Info)
}

#[derive(Debug, Copy, Clone)]
enum InfoOrExprRef<'a> {
    Expr(ExprId, &'a Expr),
    Info(InfoId, &'a Info)
}

impl Language for ExprOrTermOrInfo {
    fn children(&self) -> &[Id] {
        match self {
            ExprOrTermOrInfo::Expr(expr) => expr.children(),
            ExprOrTermOrInfo::Term(term) => term.children(),
            ExprOrTermOrInfo::Info(info) => info.children(),
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            ExprOrTermOrInfo::Expr(expr) => expr.children_mut(),
            ExprOrTermOrInfo::Term(term) => term.children_mut(),
            ExprOrTermOrInfo::Info(info) => info.children_mut(),
        }
    }

    fn matches(&self, other: &Self) -> bool {
        match (self, other) {
            (ExprOrTermOrInfo::Expr(n1), ExprOrTermOrInfo::Expr(n2)) => n1.matches(n2),
            (ExprOrTermOrInfo::Term(t1), ExprOrTermOrInfo::Term(t2)) => t1.matches(t2),
            (ExprOrTermOrInfo::Info(i1), ExprOrTermOrInfo::Info(i2)) => i1.matches(i2),
            _ => false,
        }
    }
}

pub fn map_recexpr<L1: Language + Clone, L2: Language>(mut expr: RecExpr<L1>, dummy: L1, mut f: impl FnMut(L1) -> L2) -> RecExpr<L2> {
    let mut out = RecExpr::default();
    for i in 0..expr.as_ref().len() {
        let n = mem::replace(&mut expr[Id::from(i)], dummy.clone());
        out.add(f(n));
    }

    out
}

struct Context<'a> {
    rules: &'a FxHashMap<Symbol, Rule>,
    functions: &'a FxHashMap<Symbol, Function>,
    rewrite_right: Symbol,
    rewrite_left: Symbol,
    explanation: Symbol,
    egraph: EGraph<ExprOrTermOrInfo, ()>,
    explanation_proof_memo: FxHashMap<InfoId, ProofId>,
    proof_memo: FxHashMap<(InfoOrExprId, ExprId), ProofId>,
    simplify_memo: FxHashMap<InfoOrExprId, ExprId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RuleDirection {
    Forward,
    Backward,
}

#[derive(Debug)]
pub struct Rule {
    name: Symbol,
    lhs: Pattern<ExprOrTermOrInfo>,
    rhs: Pattern<ExprOrTermOrInfo>,
    vars: Vec<Var>,
    direction: RuleDirection,
}

#[derive(Debug)]
pub struct Function {
    pub head: AppHead,
    pub congr: Symbol,
}

impl Rule {
    pub fn new(lhs: PatternAst<Expr>, rhs: PatternAst<Expr>, name: Symbol, vars: Vec<Var>, direction: RuleDirection) -> Self {
        let dummy = ENodeOrVar::ENode(Expr::Var(Symbol::new("")));
        let f = |x: ENodeOrVar<Expr>| match x {
            ENodeOrVar::ENode(n) => ENodeOrVar::ENode(ExprOrTermOrInfo::Expr(n.into())),
            ENodeOrVar::Var(v) => ENodeOrVar::Var(v),
        };
        let lhs = Pattern::new(map_recexpr(lhs, dummy.clone(), f));
        let rhs = Pattern::new(map_recexpr(rhs, dummy.clone(), f));
        Rule {name, direction, lhs, rhs, vars}
    }
}

struct LetRecExpr<L> {
    expr: RecExpr<L>,
    bindings: Vec<Id>,
    var_map: Vec<Option<usize>>,
}

impl<'a> Context<'a> {
    fn new(rules: &'a FxHashMap<Symbol, Rule>, functions: &'a FxHashMap<Symbol, Function>) -> Self {
        Context {
            rules,
            functions,
            rewrite_right: Symbol::from("Rewrite=>"),
            rewrite_left: Symbol::from("Rewrite<="),
            explanation: Symbol::from("Explanation"),
            egraph: EGraph::default(),
            explanation_proof_memo: FxHashMap::default(),
            proof_memo: FxHashMap::default(),
            simplify_memo: FxHashMap::default(),
        }
    }

    fn get_info_or_expr(&self, id: InfoOrExprId) -> InfoOrExprRef {
        match &self.egraph[id.0].nodes[0] {
            ExprOrTermOrInfo::Info(info) => InfoOrExprRef::Info(InfoId(id.0), info),
            ExprOrTermOrInfo::Expr(expr) => InfoOrExprRef::Expr(ExprId(id.0), expr),
            x => panic!("Expected info or expr, found {:?}", x),
        }
    }

    fn add_info(&mut self, v: Info) -> InfoId {
        InfoId(self.egraph.add(ExprOrTermOrInfo::Info(v)))
    }

    fn get_expr(&self, id: ExprId) -> &Expr {
        match &self.egraph[id.0].nodes[0] {
            ExprOrTermOrInfo::Expr(node) => node,
            x => panic!("Expected expr, found {:?}", x),
        }
    }

    fn add_expr(&mut self, v: Expr) -> ExprId {
        ExprId(self.egraph.add(ExprOrTermOrInfo::Expr(v)))
    }

    #[allow(dead_code)]
    fn get_proof(&self, id: ProofId) -> &Term {
        match &self.egraph[id.0].nodes[0] {
            ExprOrTermOrInfo::Term(term) => term,
            x => panic!("Expected term, found {:?}", x),
        }
    }

    fn add_proof(&mut self, v: Term) -> ProofId {
        ProofId(self.egraph.add(ExprOrTermOrInfo::Term(v)))
    }

    fn convert_sexp_to_egraph_inner(&mut self, sexp: &Sexp, let_bindings: &mut FxHashMap<Symbol, EnumInfoOrExprId>) -> Result<EnumInfoOrExprId> {
        Ok(match sexp {
            Sexp::String(s) => {
                let sym = Symbol::from(s.as_str());
                if let Some(&id) = let_bindings.get(&sym) {
                    id
                } else {
                    self.add_expr(Expr::Var(sym)).into()
                }
            },
            Sexp::List(list) => {
                if list.is_empty() {
                    bail!("Empty list in S-expression");
                }
                match &list[0] {
                    Sexp::String(s) if s == "let" => {
                        if list.len() != 3 {
                            bail!("let must have 2 arguments");
                        }
                        let binding = match &list[1] {
                            Sexp::List(x) => x,
                            _ => bail!("Let binding must be a list"),
                        };
                        if binding.len() != 2 {
                            bail!("let binding must be a list of two elements (name and value)");
                        }
                        let var = match &binding[0] {
                            Sexp::String(s) => Symbol::from(s.as_str()),
                            _ => bail!("Let variable must be a symbol"),
                        };
                        let expr = self.convert_sexp_to_egraph_inner(&binding[1], let_bindings)?;
                        let_bindings.insert(var, expr);
                        self.convert_sexp_to_egraph_inner(&list[2], let_bindings)?
                    },
                    Sexp::String(s) => {
                        let head = Symbol::from(s.as_str());
                        if let Some(direction) = self.get_rewrite_direction(&head) {
                            if list.len() != 3 {
                                anyhow::bail!("Invalid Rewrite node structure");
                            }
                            let rule_name = match &list[1] {
                                Sexp::String(s) => Symbol::new(s),
                                _ => anyhow::bail!("Rule name must be an atom"),
                            };
                            let id = match self.convert_sexp_to_egraph_inner(&list[2], let_bindings)? {
                                EnumInfoOrExprId::Expr(id) => id,
                                EnumInfoOrExprId::Info(_) => bail!("rewrite body is not a pure expr")
                            };
                            self.add_info(Info::Rewrite(direction, rule_name, id)).into()
                        } else {
                            let args = list[1..].iter()
                                .map(|item| self.convert_sexp_to_egraph_inner(item, let_bindings))
                                .collect::<Result<Vec<_>>>()?;

                            if head == self.explanation {
                                let args = args.into_iter().map(Into::into).collect();
                                self.add_info(Info::Explanation(args)).into()
                            } else {
                                let expr_args = args.iter().copied().map(|id| match id {EnumInfoOrExprId::Expr(id) => Some(id), _ => None}).collect::<Option<Vec<_>>>();
                                if let Some(expr_args) = expr_args {
                                    let func = &self.functions[&head];
                                    self.add_expr(Expr::App(func.head, expr_args)).into()
                                } else {
                                    let args = args.into_iter().map(Into::into).collect();
                                    self.add_info(Info::App(head, args)).into()
                                }
                            }
                        }
                    },
                    _ => bail!("List head must be a symbol"),
                }
            },
            Sexp::Empty => bail!("Empty S-expression not supported"),
        })
    }
    
    fn convert_sexp_to_egraph(&mut self, sexp: &Sexp) -> Result<EnumInfoOrExprId> {
        let mut let_bindings = FxHashMap::default();
        self.convert_sexp_to_egraph_inner(sexp, &mut let_bindings)
    }

    fn build_explanation_proof_term(&mut self, id: InfoId) -> Result<ProofId> {
        if let Some(&result) = self.explanation_proof_memo.get(&id) {
            return Ok(result);
        }

        let nodes = match self.get_info_or_expr(id.into()) {
            InfoOrExprRef::Info(_, Info::Explanation(args)) => {
                args.clone()
            }
            _ => bail!("expected Explanation"),
        };

        let mut proofs = Vec::new();
        for i in 1..nodes.len() {
            let prev_id = self.simplify_subtree(nodes[i - 1])?;
            let proof = self.build_proof_term(nodes[i], prev_id)?;
            proofs.push(proof);
        }
        
        let result = match proofs.len() {
            0 => bail!("Explanation with less than 2 children!"),
            1 => proofs[0],
            _ => self.add_proof(Term::Transitivity(proofs))
        };
        
        self.explanation_proof_memo.insert(id, result);
        Ok(result)
    }

    fn build_proof_term(&mut self, id: InfoOrExprId, prev_id: ExprId) -> Result<ProofId> {
        if let Some(&result) = self.proof_memo.get(&(id, prev_id)) {
            return Ok(result);
        }

        let result = if id == prev_id.into() {
            self.add_proof(Term::Reflexivity(prev_id))
        } else {
            match self.get_info_or_expr(id) {
                InfoOrExprRef::Info(id, Info::Explanation(_)) => {
                    self.build_explanation_proof_term(id)?
                },
                InfoOrExprRef::Info(_, Info::Rewrite(direction, sym, result_id)) => {
                    let direction = *direction;
                    let result_id = *result_id;
                    let rule = self.rules.get(sym).context("Rule not found")?;
                    let (lhs, rhs) = if direction == RuleDirection::Backward {
                        (&rule.rhs, &rule.lhs)
                    } else {
                        (&rule.lhs, &rule.rhs)
                    };
                    self.egraph.rebuild(); // TODO
                    //eprintln!("{:?}", rule);
                    let args = self.determine_variable_assignments(&rule.vars, lhs, rhs, prev_id, result_id)?;
                    let mut proof = self.add_proof(Term::Hypothesis(rule.name, args));
                    if direction != rule.direction {
                        proof = self.add_proof(Term::Symmetry(proof));
                    }
                    proof
                }
                InfoOrExprRef::Info(_, Info::App(head, args)) => {
                    match self.get_expr(prev_id) {
                        Expr::App(prev_head, prev_args) => {
                            let func = &self.functions[&head];
                            if func.head != *prev_head {
                                anyhow::bail!("Mismatched heads between previous and next nodes: {:?} ||| {:?}", prev_head, head);
                            }
                            if args.len() != prev_args.len() {
                                anyhow::bail!("Mismatched list lengths between previous and next nodes");
                            }
                            let args = args.clone();
                            let prev_args = prev_args.clone();
                            
                            let arg_proofs: Result<Vec<ProofId>> = args.iter().zip(prev_args.iter())
                                .map(|(&arg_id, &prev_arg_id)| self.build_proof_term(arg_id, prev_arg_id))
                                .collect();
                            
                            self.add_proof(Term::Congruence(func.congr, arg_proofs?))
                        }
                        previous => anyhow::bail!("Next node is congruence list but previous node is atom: {:?} ||| {:?} {:?}", previous, head, args),
                    }
                },
                current => anyhow::bail!("Next node is not an info but it doesn't match previous node: {:?}", current),
            }
        };

        self.proof_memo.insert((id, prev_id), result);
        Ok(result)
    }


    fn get_rewrite_direction(&self, head: &Symbol) -> Option<RuleDirection> {
        if *head == self.rewrite_right {
            Some(RuleDirection::Forward)
        } else if *head == self.rewrite_left {
            Some(RuleDirection::Backward)
        } else {
            None
        }
    }

    fn simplify_subtree(&mut self, id: InfoOrExprId) -> Result<ExprId> {
        if let Some(&result) = self.simplify_memo.get(&id) {
            return Ok(result);
        }

        let result = match self.get_info_or_expr(id) {
            InfoOrExprRef::Expr(expr_id, _expr) => expr_id,
            InfoOrExprRef::Info(_, Info::Explanation(args)) => {
                self.simplify_subtree(*args.last().context("Empty argument list")?)?
            },
            InfoOrExprRef::Info(_, Info::Rewrite(_, _, expr_id)) => {
                *expr_id
            },
            InfoOrExprRef::Info(_, Info::App(head, args)) => {
                let head = *head;
                let args = args.clone();
                
                let simplified_args: Result<Vec<ExprId>> = args.iter()
                    .map(|&arg_id| self.simplify_subtree(arg_id))
                    .collect();
                let func = &self.functions[&head];
                self.add_expr(Expr::App(func.head, simplified_args?))
            }
        };

        self.simplify_memo.insert(id, result);
        Ok(result)
    }

    fn determine_variable_assignments(&self, vars: &[Var], lhs: &Pattern<ExprOrTermOrInfo>, rhs: &Pattern<ExprOrTermOrInfo>, before: ExprId, after: ExprId) -> Result<Vec<ExprId>> {
        let mut subst = Subst::default();
        for (side, target) in [(lhs, before), (rhs, after)] {
            if let Some(matches) = side.search_eclass(&self.egraph, target.0) {
                if matches.substs.len() != 1 {
                    bail!("found {} matches instead of 1", matches.substs.len());
                }
                for &var in vars {
                    if let Some(&id) = matches.substs[0].get(var) {
                        if let Some(&existing_id) = subst.get(var) {
                            if existing_id != id {
                                bail!("Inconsistent variable assignment for {}", var);
                            }
                        } else {
                            subst.insert(var, id);
                        }
                    }
                }
            } else {
                bail!("unable to match rewrite rule from egraph explanation")
            }
        }
        vars.iter().map(|&var|
            subst.get(var).map(|&id| ExprId(id)).ok_or_else(||
                anyhow!("rule variable list has variables that don't appear on either side"))).collect()
    }
}

fn compute_reference_counts<L: Language>(expr: &RecExpr<L>) -> Vec<usize> {
    let mut ref_counts = vec![0; expr.as_ref().len()];
    for node in expr.as_ref() {
        for &child in node.children() {
            ref_counts[usize::from(child)] += 1;
        }
    }
    ref_counts
}

fn introduce_let_bindings<L: Language>(expr: RecExpr<L>) -> LetRecExpr<L> {
    let ref_counts = compute_reference_counts(&expr);
    let mut var_map = vec![None; expr.as_ref().len()];
    let mut bindings = Vec::new();

    for (id, node) in expr.as_ref().iter().enumerate() {
        if ref_counts[id] > 1 && !node.children().is_empty() {
            var_map[id] = Some(bindings.len());
            bindings.push(Id::from(id));
        }
    }

    LetRecExpr { expr, bindings, var_map }
}

struct WithParens<T>
{
    parens: bool,
    value: T
}

impl<T> WithParens<T>
{
    fn new_token(value: T) -> Self {
        WithParens {parens: false, value}
    }

    fn new_expr(value: T) -> Self {
        WithParens {parens: true, value}
    }

    fn without_parens(self) -> T {
        self.value
    }
}

impl<T: Display> Display for WithParens<T>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.parens {
            f.write_char('(')?;
        }

        self.value.fmt(f)?;

        if self.parens {
            f.write_char(')')?;
        }

        Ok(())
    }
}

fn expr_or_term_inner_to_string(rec_expr: &LetRecExpr<ExprOrTermOrInfo>, id: Id) -> WithParens<String> {
    //eprintln!("enter {}: {:?}", id, &expr.expr[id]);
    match &rec_expr.expr[id] {
        ExprOrTermOrInfo::Info(info) => panic!("unexpected info node in expr_or_term_inner_to_string: {:?}", info),
        ExprOrTermOrInfo::Expr(expr) => match expr {
            Expr::Var(s) => WithParens::new_token(s.to_string()), // skip parens
            Expr::App(head, args) => {
                let args_str: Vec<_> = args.iter().map(|&arg_id| node_or_term_to_string(rec_expr, arg_id.0)).collect();
                WithParens::new_expr(if head.fixity == Fixity::Infix && args.len() == 2 {
                    format!("{} {} {}", args_str[0], head.symbol, args_str[1])
                } else {
                    format!("{} {}", head.symbol, args_str.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" "))
                })
            }
        },
        ExprOrTermOrInfo::Term(term) => match term {
            Term::Hypothesis(name, args) => {
                if args.is_empty() {
                    WithParens::new_token(name.to_string())
                } else {
                    let assignments_str = args.iter()
                        .map(|&id| format!("{}", node_or_term_to_string(rec_expr, id.0)))
                        .collect::<Vec<_>>()
                        .join(" ");
                    WithParens::new_expr(format!("{} {}", name, assignments_str))
                }
            }
            Term::Reflexivity(expr_id) => {
                let term = node_or_term_to_string(rec_expr, expr_id.0);
                WithParens::new_expr(format!("R {}", term))
            }
            Term::Symmetry(proof_id) => {
                WithParens::new_expr(format!("S {}", node_or_term_to_string(rec_expr, proof_id.0)))
            }
            Term::Transitivity(proof_ids) => {
                proof_ids.iter().skip(1).fold(
                    node_or_term_to_string(rec_expr, proof_ids[0].0),
                    |acc, &proof_id| {
                        WithParens::new_expr(format!("T {} {}", acc, node_or_term_to_string(rec_expr, proof_id.0)))
                    }
                )
            }
            Term::Congruence(op, proof_ids) => {
                let args_str = proof_ids
                    .iter()
                    .map(|&proof_id| node_or_term_to_string(rec_expr, proof_id.0).to_string())
                    .collect::<Vec<_>>()
                    .join(" ");
                WithParens::new_expr(format!("{} {}", op, args_str))
            }
        }
    }
}

fn node_or_term_to_string(expr: &LetRecExpr<ExprOrTermOrInfo>, id: Id) -> WithParens<String> {
    if let Some(var_idx) = expr.var_map[usize::from(id)] {
        WithParens::new_token(match expr.expr[id] {
            ExprOrTermOrInfo::Expr(_) => format!("v{}", var_idx),
            ExprOrTermOrInfo::Term(_) => format!("h{}", var_idx),
            ExprOrTermOrInfo::Info(_) => panic!("unexpected info node in node_or_term_to_string")
        })
    } else {
        expr_or_term_inner_to_string(expr, id)
    }
}

pub fn convert_explanation_to_lean_proof(sexp: &Sexp, rules: &FxHashMap<Symbol, Rule>, functions: &FxHashMap<Symbol, Function>) -> Result<String> {
    let mut ctx = Context::new(rules, functions);

    let root_id = match ctx.convert_sexp_to_egraph(sexp)? {
        EnumInfoOrExprId::Expr(_) => bail!("pure expr at proof root"),
        EnumInfoOrExprId::Info(id) => id
    };
    let proof_id = ctx.build_explanation_proof_term(root_id)?;

    let extractor = Extractor::new(&ctx.egraph, AstSize);
    let (_, expr) = extractor.find_best(proof_id.0);
    /*
    for (i, e) in expr.as_ref().iter().enumerate() {
        eprintln!("{} = {:?}", i, e);
    }
    */
    let expr = introduce_let_bindings(expr);

    let mut result = String::new();

    for (idx, id) in expr.bindings.iter().enumerate() {
        let (kw, c) = match expr.expr[*id] {
            ExprOrTermOrInfo::Expr(_) => ("let", "v"),
            ExprOrTermOrInfo::Term(_) => ("have", "h"),
            ExprOrTermOrInfo::Info(_) => panic!("unexpected info node in convert_explanation_to_lean_proof"),
        };
        result.push_str(&format!("{} {}{} := {}\n", kw, c, idx, expr_or_term_inner_to_string(&expr, *id).without_parens()));
    }

    result.push_str(&node_or_term_to_string(&expr, Id::from(expr.expr.as_ref().len() - 1)).without_parens());
    
    Ok(result)
}
