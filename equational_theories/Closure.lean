import equational_theories.EquationalResult

namespace Closure
open Lean Parser Elab Command

inductive Edge
  | implication : Implication → Edge
  | nonimplication : Implication → Edge
  deriving DecidableEq, Hashable

def Edge.isTrue : Edge → Bool
  | .implication _ => true
  | .nonimplication _ => false

def Edge.get : Edge → Implication
  | .nonimplication x | .implication x => x

def Edge.lhs : Edge → String := Implication.lhs ∘ get

def Edge.rhs : Edge → String := Implication.rhs ∘ get

inductive Outcome
  /-- the implication has an explicit proof -/
  | explicit_proof_true
  /-- the implication can be derived from proven theorems -/
  | implicit_proof_true
  /-- the implication is explicitly conjectured -/
  | explicit_conjecture_true
  /-- the implication can be derived from theorems and conjectures -/
  | implicit_conjecture_true
  /-- the status of the implication is unknown -/
  | unknown
  /-- the implication can be disproved from theorems and conjectures -/
  | implicit_conjecture_false
  /-- the implication can is explicitly conjectured to be false -/
  | explicit_conjecture_false
  /-- the falsity of the implication can be derived from proven theorems -/
  | implicit_proof_false
  /-- the implication has an explicit disproof -/
  | explicit_proof_false
  deriving Repr, DecidableEq, Hashable, Lean.ToJson, Lean.FromJson

instance : Inhabited Outcome where
  default := .unknown

instance : ToString Outcome where
  toString
  | .unknown => "\"unknown\""
  | .explicit_proof_true => "\"explicit_proof_true\""
  | .implicit_proof_true => "\"implicit_proof_true\""
  | .explicit_proof_false => "\"explicit_proof_false\""
  | .implicit_proof_false => "\"implicit_proof_false\""
  | .explicit_conjecture_true => "\"explicit_conjecture_true\""
  | .implicit_conjecture_true => "\"implicit_conjecture_true\""
  | .explicit_conjecture_false => "\"explicit_conjecture_false\""
  | .implicit_conjecture_false => "\"implicit_conjecture_false\""

def Outcome.implicit_theorem : Bool → Outcome
  | true => implicit_proof_true
  | false => implicit_proof_false

def Outcome.explicit_theorem : Bool → Outcome
  | true => explicit_proof_true
  | false => explicit_proof_false

def Outcome.implicit_conjecture : Bool → Outcome
  | true => implicit_conjecture_true
  | false => implicit_conjecture_false

def Outcome.explicit_conjecture : Bool → Outcome
  | true => explicit_conjecture_true
  | false => explicit_conjecture_false

def Outcome.isExplicit : Outcome → Bool
  | explicit_proof_true => true
  | implicit_proof_true => false
  | explicit_conjecture_true => true
  | implicit_conjecture_true => false
  | unknown => false
  | implicit_conjecture_false => false
  | explicit_conjecture_false => true
  | implicit_proof_false => false
  | explicit_proof_false => true

def Outcome.isProven : Outcome → Bool
  | explicit_proof_true => true
  | implicit_proof_true => true
  | explicit_conjecture_true => false
  | implicit_conjecture_true => false
  | unknown => false
  | implicit_conjecture_false => false
  | explicit_conjecture_false => false
  | implicit_proof_false => true
  | explicit_proof_false => true

def Outcome.isTrue : Outcome → Bool
  | explicit_proof_true => true
  | implicit_proof_true => true
  | explicit_conjecture_true => true
  | implicit_conjecture_true => true
  | unknown => false
  | implicit_conjecture_false => false
  | explicit_conjecture_false => false
  | implicit_proof_false => false
  | explicit_proof_false => false

partial def dfs1 (graph : Array (Array Nat)) (vertex : Nat) (vis : Array Bool) (order : Array Nat) :
    Array Bool × Array Nat := Id.run do
  let mut vis1 := vis.set! vertex true
  let mut ord := order
  for v in graph[vertex]! do
    unless vis1[v]! do
      (vis1, ord) := dfs1 graph v vis1 ord
  pure (vis1, ord.push vertex)

partial def dfs2 (graph : Array (Array Nat)) (vertex : Nat) (component : Array Nat) (component_id : Nat) :
    Array Nat := Id.run do
  let mut comp := component.set! vertex component_id
  for v in graph[vertex]! do
    if component[v]! == 0 then
      comp := dfs2 graph v comp component_id
  pure comp

/-- This is a bitset (https://en.cppreference.com/w/cpp/utility/bitset).
It represents an array of bits by directly packing them to UInt64, which makes some operations
more efficient. This is also more space-efficient. -/
def Bitset := Array UInt64

def Bitset.toArray : Bitset → Array UInt64 := id

instance : Inhabited Bitset := ⟨#[]⟩

def Bitset.mk (n : Nat) : Bitset := Array.mkArray ((n + 63) >>> 6) 0

def Bitset.set (b : Bitset) (n : Nat) : Bitset :=
  b.modify (n >>> 6) (fun x ↦ x ||| (1 <<< ((UInt64.ofNat n) &&& 63)))

def Bitset.get (b : Bitset) (n : Nat) : Bool :=
  (b.toArray[n >>> 6]! >>> ((UInt64.ofNat n) &&& 63)) &&& 1 != 0

def number_equations (inp : Array EntryVariant) : Std.HashMap String Nat × Array String := Id.run do
  -- number the equations (arbitrarily) for easier processing
  let mut eqs : Std.HashMap String Nat := {}
  let mut eqs_order : Array String := #[]
  for imp in inp do
    match imp with
    | .implication ⟨lhs, rhs⟩ =>
      match eqs.containsThenInsertIfNew lhs eqs.size with
      | (n, neqs) =>
        eqs := neqs
        unless n do eqs_order := eqs_order.push lhs
      match eqs.containsThenInsertIfNew rhs eqs.size with
      | (n, neqs) =>
        eqs := neqs
        unless n do eqs_order := eqs_order.push rhs
    | .facts ⟨satisfied, refuted⟩ =>
      for lhs in satisfied ++ refuted do
        match eqs.containsThenInsertIfNew lhs eqs.size with
      | (n, neqs) =>
        eqs := neqs
        unless n do eqs_order := eqs_order.push lhs
    | _ => pure ()
  pure (eqs, eqs_order)

/--
This transforms the `Facts` in the input array to `Edge`s
-/
def toEdges (inp : Array EntryVariant) : Array Edge := Id.run do
  let (eqs, eqs_order) := number_equations inp
  let mut edges : Array Edge := Array.mkEmpty inp.size
  let mut nonimplies : Array Bitset := Array.mkArray eqs.size (Bitset.mk eqs.size)
  for imp in inp do
    match imp with
    | .implication ⟨lhs, rhs⟩ =>
      edges := edges.push (.implication ⟨lhs, rhs⟩)
    | .facts ⟨satisfied, refuted⟩ =>
      for f1 in satisfied do
        for f2 in refuted do
          nonimplies := nonimplies.modify eqs[f1]! (fun x ↦ x.set eqs[f2]!)
    | _ => continue
  for i in [:eqs.size] do
    for j in [:eqs.size] do
      if nonimplies[i]!.get j then
        edges := edges.push (.nonimplication ⟨eqs_order[i]!, eqs_order[j]!⟩)
  return edges

structure Reachability where
  size : Nat
  reachable : Array Bitset
  components : Array (Array Nat)

def closure_aux (inp : Array EntryVariant) (eqs : Std.HashMap String Nat) : Reachability := Id.run do

  -- construct the implication/non-implication graph
  let n := eqs.size
  let mut graph_size := 2 * n
  let mut graph : Array (Array Nat) := Array.mkArray graph_size #[]
  let mut revgraph : Array (Array Nat) := Array.mkArray graph_size #[]
  for imp in inp do
    match imp with
    | .implication imp =>
      graph := graph.modify (eqs[imp.rhs]!) (fun x => x.push eqs[imp.lhs]!)
      graph := graph.modify (eqs[imp.rhs]! + n) (fun x => x.push (eqs[imp.lhs]! + n))
      revgraph := revgraph.modify (eqs[imp.lhs]!) (fun x => x.push eqs[imp.rhs]!)
      revgraph := revgraph.modify (eqs[imp.lhs]! + n) (fun x => x.push (eqs[imp.rhs]! + n))
    | .facts ⟨satisfied, refuted⟩ =>
      if satisfied.size * refuted.size < satisfied.size + refuted.size + 1 then
        for lhs in satisfied do
          for rhs in refuted do
            graph := graph.modify (eqs[lhs]!) (fun x => x.push (eqs[rhs]! + n))
            revgraph := revgraph.modify (eqs[rhs]! + n) (fun x => x.push eqs[lhs]!)
      else
        let dummy := graph_size
        graph_size := graph_size + 1
        graph := graph.push (refuted.map (eqs[·]! + n))
        revgraph := revgraph.push (satisfied.map (eqs[·]!))
        for f1 in satisfied do
          graph := graph.modify eqs[f1]! (fun x ↦ x.push dummy)
        for f1 in refuted do
          revgraph := revgraph.modify (eqs[f1]! + n) (fun x ↦ x.push dummy)
    | _ => pure ()

  let mut vis : Array Bool := Array.mkArray graph_size false
  let mut order : Array Nat := Array.mkEmpty graph_size

  -- compute strongly connected components and the condensation graph using Kosaraju's algorithm
  for i in [:graph_size] do
    unless vis[i]! do
      (vis, order) := dfs1 graph i vis order

  order := order.reverse

  let mut component : Array Nat := Array.mkArray graph_size 0
  let mut last_component : Nat := 0


  for i in order do
    if component[i]! == 0 then do
      last_component := last_component + 1
      component := dfs2 revgraph i component last_component

  let mut components : Array (Array Nat) := Array.mkArray last_component #[]
  let mut comp_graph : Array (Std.HashSet Nat) := Array.mkArray last_component {}

  for i in [:graph_size] do
    components := components.modify (component[i]!-1) (fun x ↦ x.push i)
    for j in graph[i]! do
      unless component[i]! == component[j]! do
        comp_graph := comp_graph.modify (component[i]!-1) (fun x ↦ x.insert (component[j]!-1))

  -- Run bitset transitive closure on the condensation graph
  let mut reachable : Array Bitset := Array.mkArray last_component (Bitset.mk last_component)

  for i_ in [:last_component] do
    let i := last_component - 1 - i_
    reachable := reachable.modify i (fun x ↦ x.set i)
    for j in comp_graph[i]! do
      reachable := reachable.modify i (fun x ↦ x.mapIdx (fun idx val ↦
        reachable[j]!.toArray[idx]! ||| val))

  pure ⟨n, reachable, components⟩

instance {m : Type → Type} : ForIn m Reachability (Nat × Nat × Bool) where
  forIn {β : Type} [Monad m] (reachability : Reachability) (state : β)
      (f : (Nat × Nat × Bool) → β → m (ForInStep β)) := do
    let mut v := state
    for i in reachability.components, i2 in reachability.reachable do
      if i.back >= reachability.size then continue
      for j in reachability.components, j2 in [:reachability.components.size] do
        if i2.get j2 then
          for x in i do
            for y in j do
              if x == y || y >= reachability.size * 2 then continue
              let val := if y < reachability.size then (y, x, true) else (x, y - reachability.size, false)
              match ← f val v with
              | .done a => return a
              | .yield a => v := a
    return v

/--
This computes the closure of the implications/non-implications represented by `inp`.
-/
def closure (inp : Array EntryVariant) : Array Edge := Id.run do
  let (eqs, eqs_order) := number_equations inp
  let n := eqs.size


  -- extract the implications
  let mut ans : Array Edge := Array.mkEmpty (n*n)

  for ⟨x, y, is_true⟩ in closure_aux inp eqs do
    if is_true then
      ans := ans.push (.implication ⟨eqs_order[x]!, eqs_order[y]!⟩)
    else
      ans := ans.push (.nonimplication ⟨eqs_order[x]!, eqs_order[y]!⟩)

  pure ans

def list_outcomes {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (Array String × Array (Array Outcome)) := do
  let rs := (← Result.extractEquationalResults).map (·.variant)
  let prs := ((← Result.extractTheorems).map (·.variant))
  let (eqs, eqs_order) := number_equations rs
  let n := eqs.size
  let mut outcomes : Array (Array Outcome) := Array.mkArray n (Array.mkArray n .unknown)
  for edge in toEdges prs do
    outcomes := outcomes.modify eqs[edge.lhs]! (fun a ↦ a.set! eqs[edge.rhs]!
      (.explicit_theorem edge.isTrue))

  for ⟨x, y, is_true⟩ in closure_aux prs eqs do
    outcomes := outcomes.modify x (fun a ↦ a.modify y
                fun y ↦ if y = .unknown then .implicit_theorem is_true else y)

  for edge in toEdges rs do
    outcomes := outcomes.modify eqs[edge.lhs]! (fun a ↦ a.modify eqs[edge.rhs]!
      fun y ↦ if y = .unknown then .explicit_conjecture edge.isTrue else y)

  for ⟨x, y, is_true⟩ in closure_aux rs eqs do
    outcomes := outcomes.modify x (fun a ↦ a.modify y
                fun y ↦ if y = .unknown then .implicit_conjecture is_true else y)

  return (eqs_order, outcomes)

def outcomes_mod_equiv (inp : Array EntryVariant) : Array String × Array (Array (Option Bool)) := Id.run do
  let (eqs, eqs_order) := number_equations inp
  let n := eqs.size
  let reachable := closure_aux inp eqs
  let mut reprs_id : Std.HashMap Nat Nat := {}
  let mut reprs : Array String := Array.mkEmpty (reachable.components.size / 2)
  for comp in reachable.components do
    if comp[0]! < n then
      reprs_id := reprs_id.insert comp[0]! reprs.size
      reprs := reprs.push eqs_order[comp[0]!]!

  let mut implies : Array (Array (Option Bool)) :=
    Array.mkArray reprs.size (Array.mkArray reprs.size none)

  for i in reachable.components, i2 in reachable.reachable do
    if i[0]! >= reachable.size then continue
      for j in reachable.components, j2 in [:reachable.components.size] do
        if i2.get j2 then
          if j[0]! < n then
            implies := implies.modify reprs_id[j[0]!]! (fun x ↦ x.set! reprs_id[i[0]!]! true)
          else if j.back < 2*n then
            implies := implies.modify reprs_id[i[0]!]! (fun x ↦ x.set! reprs_id[j[0]! - n]! false)

  return (reprs, implies)

end Closure
