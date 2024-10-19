import equational_theories.Confluence

namespace Confluence

open Lean.Parser.Tactic

attribute [confluence_simps] not_true_eq_false not_false_eq_true false_implies implies_true imp_false false_and and_true and_self not_and and_imp
attribute [confluence_simps] ite_eq_right_iff
attribute [confluence_simps] Option.ite_none_right_eq_some Option.some.injEq
attribute [confluence_simps] forall_apply_eq_imp_iff₂
attribute [confluence_simps] FreeMagma.Fork.injEq

simproc [confluence_simps] confluenceReduceCtorEq (_) := reduceCtorEq

-- for some reason if I try to use Not.eq_def directly from a tactic it can't find it!
private def not_eq_def := Not.eq_def

scoped macro "separate" : tactic => `(tactic| (
  try simp only [Not.eq_def]
  try intros
  try injections
  try casesm* _ ∨ _, _ ∧ _, Exists _
  try any_goals
    try subst_eqs
    try trivial
))

scoped macro "prove_elim" : tactic => `(tactic| (
  repeat' split
  all_goals simp_all only [confluence_simps, exists_and_right, exists_eq_right_right', exists_eq_right', false_iff, not_exists, true_and]
  separate
  try simp_all only [not_true_eq_false, imp_false]
  try
    constructor
    · intro h
      subst_eqs
      repeat constructor
    · separate
  try any_goals
    try separate
    try simp_all only [not_true_eq_false, imp_false]
))

scoped macro "prove_elim_not" : tactic => `(tactic| (
  repeat' split
  all_goals simp_all only [confluence_simps, false_iff, not_exists, not_and, true_iff, forall_eq', forall_apply_eq_imp_iff, true_iff, not_false_eq_true]
  separate
  try simp_all only [not_true_eq_false, imp_false]
  try any_goals separate
  try any_goals
    try simp_all only [not_true_eq_false, imp_false]
    try rename_i h
    try apply h
    try any_goals apply Eq.refl _
    try any_goals trivial
))

open Lean hiding HashMap
open Meta Elab Command Term Parser Syntax
open Std (HashMap)

scoped syntax (name := ruleSystem) "rule_system " ident " {" ident* " : " term "}" ("-" ident)* (ppLine "|" term "=>" term)+ : command

private partial def makePattern (inc: Nat) : Syntax → StateM (HashMap Name Nat) (TSyntax `term)
| .node info kind args => do
  pure <| TSyntax.mk <| Syntax.node info kind (← args.mapM (makePattern inc ·))
| s@(.ident _ _ name _) =>
  modifyGet (λ m ↦ match m[name]? with
  | some n => ((mkIdentFrom s (.mkSimple s!"{name}{n}")), m.insert name (n + inc))
  | _ => (TSyntax.mk s, m))
| s@_ => pure <| TSyntax.mk s

private partial def countVars : Syntax → StateM (HashMap Name Nat) Unit
| .node _ _ args => args.forM countVars
| .ident _ _ name _ => modify (λ m ↦ match m[name]? with
  | some n => m.insert name (n + 1)
  | _ => m)
| _ => pure ()

scoped macro_rules
| `(command| rule_system $system:ident {$vars:ident* : $type:term} $[-$disable:ident]* $[| $lhs:term => $rhs:term]*) => do
  let mut decls := #[]

  let mut ruleIdents := #[]
  let mut ruleElims := #[]
  let mut ruleElimNots := #[]
  let mut ruleUsedVars := #[]

  let systemName := system.getId
  let numRules := lhs.size

  for idx in [:numRules] do
    let lhs := TSyntax.mk <| lhs[idx]!
    let rhs := TSyntax.mk <| rhs[idx]!
    let mut varSet := Std.HashMap.empty
    for var in vars do
      varSet := varSet.insert var.getId 0
    let (_, varCounts) := StateT.run (countVars lhs) varSet

    let mut varIdx := Std.HashMap.empty
    for (name, count) in varCounts do
      if count > 1 then
        varIdx := varIdx.insert name 1

    let (lhsP, _) := StateT.run (makePattern 1 lhs) varIdx
    let (rhsP, _) := StateT.run (makePattern 0 rhs) varIdx

    let mut cond := none
    for var in vars.reverse do
      let varName := var.getId
      for n in (List.range <| (varCounts.getD varName 0) - 1).reverse do
        let id1 := Lean.mkIdent <| .mkSimple s!"{varName}{n + 1}"
        let id2 := Lean.mkIdent <| .mkSimple s!"{varName}{n + 2}"
        let eq := mkCApp `Eq #[id1, id2]
        cond := some <| match cond with
        | none => eq
        | some e => mkCApp `And #[eq, e]

    let rhsP ← match cond with
    | some cond' => `(if $cond' then some $rhsP else none)
    | none => `(some $rhsP)

    let ruleName := .str systemName s!"rule{idx+1}"
    let ruleId := Lean.mkIdent ruleName
    ruleIdents := ruleIdents.push ruleId
    decls := decls.push <| ← `(
      set_option linter.unusedVariables false in
      def $ruleId : $type → Option ($type)
      | $lhsP => $rhsP
      | _ => none
    )

    let usedVars := vars.filter (λ v ↦ varCounts.getD (v.getId) 0 > 0)
    ruleUsedVars := ruleUsedVars.push usedVars

    let elim := Lean.mkIdent <| .str (ruleName) "elim"
    ruleElims := ruleElims.push elim
    decls := decls.push <| ← `(
      def $elim (e r: $type): $ruleId e = some r ↔
          ∃ $[$usedVars:ident]*, e = $lhs ∧ r = $rhs := by
        simp only [$ruleId:ident]
        prove_elim
    )

    let elimNot := Lean.mkIdent <| .str (ruleName) "elim_not"
    ruleElimNots := ruleElimNots.push elimNot
    decls := decls.push <| ← `(
      def $elimNot (e: $type): $ruleId e = none ↔
        ¬∃ $[$usedVars:ident]*, e = $lhs := by
        simp only [$ruleId:ident]
        prove_elim_not
    )

  let mut ruleEqs := #[]
  let mut body := ← `(x)
  for inner in (List.range numRules).reverse do
    body := (← `(
      match $(ruleIdents[inner]!):ident x with
      | some x => x
      | none => $body
    ))

  decls := decls.push <| ← `(
    def $system (x: $type): $type :=
      $body
  )

  for idx in [:numRules] do
    let eq := Lean.mkIdent <| .str systemName s!"eq{idx+1}"
    ruleEqs := ruleEqs.push eq
    decls := decls.push <| ← `(
      def $eq ($(ruleUsedVars[idx]!)*: $type):
        $system $(TSyntax.mk <| lhs[idx]!):term = $(TSyntax.mk <| rhs[idx]!):term := by
        simp only [$system:ident]
        repeat' split
        $[· simp_all only [$ruleElims:ident]; separate]*
        · have h : $(ruleIdents[idx]!):ident (?x : $type) = none := by
            assumption
          simp only [$(ruleElimNots[idx]!):ident, not_exists] at h
          exfalso
          apply h
          separate
    )

  let or := (← ruleIdents.mapM (λ n ↦ `($n e = some r))).foldr (init := none) λ
  | x, some s => mkCApp `Or #[x, s]
  | x, none => x

  let andNot := (← ruleIdents.mapM (λ n ↦ `($n e = none))).foldr (init := none) λ
  | x, some s => mkCApp `And #[x, s]
  | x, none => x

  let elim' := Lean.mkIdent <| .str systemName "elim'"
  let cases ← (ruleElims.zip ruleEqs).mapM (λ (l1, l2) ↦ `(tactic| · simp_all only [$l1:ident]; separate; simp_all only [$l2:ident]))
  decls := decls.push <| ← `(
    def $elim' (e r: $type): $system e = r ↔
        $(or.get!) ∨ (e = r ∧ $(andNot.get!)) := by
      constructor
      · intro h
        simp only [$system:ident] at h
        repeat' split at h
        all_goals simp_all only [or_self, and_self, or_true, true_or, and_true, true_and]
      · intro h
        separate
        $[$cases];*
        simp_all only [$system:ident]
  )

  let elim := Lean.mkIdent <| .str systemName "elim"
  decls := decls.push <| ← `(
    def $elim (e r: $type) := by
      simpa only [$[$ruleElims:ident],*, $[$ruleElimNots:ident],*] using $elim' e r
  )

  if ¬disable.any (·.getId == `IsProj) then
    let instIsProj := Lean.mkIdent <| .str systemName "instIsProj"
    decls := decls.push <| ← `(
      open Confluence in
      instance $instIsProj:ident : FreeMagma.IsProj ($system : $type → $type) where
        proj := by
          intro x
          generalize h: $system x = e
          simp only [$elim:ident] at h
          separate
          all_goals subterm
    )

  pure <| mkListNode decls

end Confluence
