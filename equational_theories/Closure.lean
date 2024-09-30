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
  | explicit_proof_true
  | implicit_proof_true
  | explicit_conjecture_true
  | implicit_conjecture_true
  | unknown
  | implicit_conjecture_false
  | explicit_conjecture_false
  | implicit_proof_false
  | explicit_proof_false
  deriving Repr, DecidableEq, Hashable, Lean.ToJson, Lean.FromJson

instance : Inhabited Outcome where
  default := .unknown

instance : ToString Outcome where
  toString := toString ∘ repr

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

def Bitset := Array UInt64

def Bitset.toArray : Bitset → Array UInt64 := id

instance : Inhabited Bitset := ⟨#[]⟩

def Bitset.mk (n : Nat) : Bitset := Array.mkArray ((n + 63) >>> 6) 0

def Bitset.set (b : Bitset) (n : Nat) : Bitset :=
  b.modify (n >>> 6) (fun x ↦ x ||| (1 <<< ((UInt64.ofNat n) &&& 63)))

def Bitset.get (b : Bitset) (n : Nat) : Bool :=
  (b.toArray[n >>> 6]! >>> ((UInt64.ofNat n) &&& 63)) &&& 1 != 0

def toEdges (inp : Array EntryVariant) : IO (Array Edge) := do
  let mut edges : Std.HashSet Edge := {}
  for imp in inp do
    -- println! "Running, size {edges.size}"
    match imp with
    | .implication ⟨lhs, rhs⟩ =>
      -- println! "Implication"
      edges := edges.insert (.implication ⟨lhs, rhs⟩)
    | .facts ⟨satisfied, refuted⟩ =>
      -- println! "Facts {satisfied[0]?} {refuted[0]?}"
      for f1 in satisfied do
        -- println! "Processing {f1}"
        for f2 in refuted do
          -- println! "Sub-Processing {f2}"
          edges := edges.insert (.nonimplication ⟨f1, f2⟩)
    | _ => continue
  -- println! "Done"
  return edges.toArray

def closure (inp : Array EntryVariant) : IO (Array Edge) := do
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

  -- extract the implications
  let mut ans : Array Edge := Array.mkEmpty (n*n)


  for i in [:last_component] do
    if components[i]!.back >= n then continue
    for j in [:last_component] do
      if reachable[i]!.get j then
        for x in components[i]! do
          for y in components[j]! do
            if x == y then continue
            if y < n then
              ans := ans.push (.implication ⟨eqs_order[y]!, eqs_order[x]!⟩)
            else if y < 2*n then
              ans := ans.push (.nonimplication ⟨eqs_order[x]!, eqs_order[y - n]!⟩)

  pure ans

end Closure
