import equational_theories.Generated
import equational_theories.Equations.LawsComplete

namespace ImpGraph

def Graph := Nat

instance : OrOp Graph := inferInstanceAs (OrOp Nat)
instance : AndOp Graph := inferInstanceAs (AndOp Nat)
instance : BEq Graph := inferInstanceAs (BEq Nat)
instance : Lean.ToExpr Graph := inferInstanceAs (Lean.ToExpr Nat)
instance : DecidableEq Graph := inferInstanceAs (DecidableEq Nat)

def Graph.singleton (i j : Fin 4694) : Graph :=
  Nat.shiftLeft 1 (i.val * 4694 + j.val)

def Graph.empty : Graph := (0 : Nat)

def Graph.isEmpty (g : Graph) : Bool :=
  g == .empty

def Graph.get (g : Graph) (i j : Fin 4694) : Bool :=
  -- Bool.not (Nat.beq (Nat.land g (Graph.singleton i j)) 0)
  !(g &&& (Graph.singleton i j)).isEmpty

theorem Nat_or_eq_zero (n m : Nat) : ((n ||| m) == 0) = (n == 0 && m == 0) := by
  sorry

@[simp] theorem Graph.union_get (g1 g2 : Graph) (i j : Fin 4694) :
  (g1 ||| g2).get i j = (g1.get i j || g2.get i j) := by
  simp [Graph, get, Graph.isEmpty, Graph.empty, Nat.and_distrib_right, Nat_or_eq_zero]

def Graph.models (g : Graph) (P : (i j : Nat) → Prop) :=
  ∀ i j, g.get i j → P i j

@[simp]
theorem Graph.empty_models (P : (i j : Nat) → Prop) : Graph.empty.models P :=
  sorry

@[simp]
theorem Graph.singleton_models (P : (i j : Nat) → Prop) (i j : Fin 4694)  :
    (Graph.singleton i j).models P ↔ P i j := by
  simp [models, singleton, get]
  sorry

theorem Graph.union_models (g1 g2 : Graph) (P : (i j : Nat) → Prop) :
    g1.models P → g2.models P → (g1 ||| g2).models P := by
  simp [models]; tauto

open Lean Elab in
elab "defineImpGraph%" : term => do
  let rs ← Result.extractTheorems
  -- let rs := rs[:20] -- use this to speed up testing
  let mut pairs := #[]
  let mut graph : Graph := .empty
  for r in rs do
    if let .implication ⟨lhs, rhs⟩ := r.variant then
      -- logInfo m!"{lhs} => {rhs}"
      let some n1 := lhs.replace "Equation" "" |>.toNat? | throwError "Cannot parse {lhs}"
      let some n2 := rhs.replace "Equation" "" |>.toNat? | throwError "Cannot parse {rhs}"
      unless n1 ≤ 4694 do continue
      unless n2 ≤ 4694 do continue
      let i := n1-1
      let j := n2-1
      pairs := pairs.push (n1-1,n2-1)
      graph := graph ||| .singleton i j

  return mkNatLit graph

def impGraph : Graph := defineImpGraph%

/-- info: 2 -/
#guard_msgs in
#eval Nat.log2 impGraph / (8*1024*1024) -- size in MB

/-- info: true -/
#guard_msgs in
#eval impGraph.get 591 590 -- Equation592 => Equation591

def lawImplication (i j : Nat) := (laws[i].implies laws[j])

inductive ImpEntries where
  | empty
  | node : ImpEntries → ImpEntries → ImpEntries
  | leaf : (i j : Nat) → lawImplication i j → ImpEntries

def ImpEntries.graph : ImpEntries → Graph
  | .empty => .empty
  | .node ie1 ie2 => ie1.graph ||| ie2.graph
  | .leaf i j _ =>
    if i < 4694 && j < 4694 then
      .singleton i j
    else
      .empty

open Lean Elab in
elab "defineImpEntries%" : term => do
  let rs ← Result.extractTheorems
  -- let rs := rs[:20] -- use this to speed up testing
  let mut entries : Array Expr := #[]
  for r in rs do
    if let .implication ⟨lhs, rhs⟩ := r.variant then
      let some n1 := lhs.replace "Equation" "" |>.toNat? | throwError "Cannot parse {lhs}"
      let some n2 := rhs.replace "Equation" "" |>.toNat? | throwError "Cannot parse {rhs}"
      unless n1 ≤ 4694 do continue
      unless n2 ≤ 4694 do continue
      let i := n1-1
      let j := n2-1
      let lawThmName : Name := Name.mkSimple s!"Law{n1}_implies_Law{n2}"
      entries := entries.push <|
        mkApp3 (mkConst ``ImpEntries.leaf) (toExpr i) (toExpr j) (mkConst lawThmName)

  let rec go (lb ub : Nat) (h1 : lb < ub) (h2 : ub ≤ entries.size) : Lean.Expr :=
    if h : lb + 1 = ub then
      entries[lb]
    else
      let mid := (lb + ub)/2
      mkApp2 (mkConst ``ImpEntries.node)
        (go lb mid (by omega) (by omega)) (go mid ub (by omega) h2)
  if h : 0 < entries.size then
    return go 0 entries.size h (Nat.le_refl _)
  else
    return mkConst ``ImpEntries.empty

def impEntries : ImpEntries := defineImpEntries%

theorem impGraph_from_impEntries : impGraph = impEntries.graph := by
  native_decide


theorem ImpEntries.graph_correct (ie : ImpEntries) : ie.graph.models lawImplication := by
  induction ie using graph.induct
  · simp [graph]
  · simp [graph]
    apply Graph.union_models <;> assumption
  · simp_all [graph, Nat.mod_eq_of_lt]
  · simp [graph, Nat.mod_eq_of_lt, *]


theorem impGraph_correct : impGraph.models (fun i j => laws[i].implies laws[j]) := by
  rw [impGraph_from_impEntries]
  exact ImpEntries.graph_correct _
