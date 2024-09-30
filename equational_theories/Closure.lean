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

def EntryVariant.toEdge? : EntryVariant → Option Edge
  | .implication x => some (.implication x)
  | .nonimplication x => some (.nonimplication x)
  | _ => none

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

instance : HOr Bitset Bitset Bitset where
  hOr a b := a.zipWith b (· ||| ·)

def closure (inp : Array Edge) : Array Edge := Id.run do
  -- number the equations (arbitrarily) for easier processing
  let mut eqs : Std.HashMap String Nat := {}
  let mut eqs_order : Array String := #[]
  for imp in inp do
    match eqs.containsThenInsertIfNew imp.lhs eqs.size with
    | (n, neqs) =>
      eqs := neqs
      unless n do eqs_order := eqs_order.push imp.lhs
    match eqs.containsThenInsertIfNew imp.rhs eqs.size with
    | (n, neqs) =>
      eqs := neqs
      unless n do eqs_order := eqs_order.push imp.rhs

  -- construct the implication/non-implication graph
  let n := eqs.size
  let mut graph : Array (Array Nat) := Array.mkArray (2 * n) #[]
  let mut revgraph : Array (Array Nat) := Array.mkArray (2 * n) #[]
  for imp in inp do
    match imp with
    | .implication imp =>
      graph := graph.modify (eqs[imp.rhs]!) (fun x => x.push eqs[imp.lhs]!)
      graph := graph.modify (eqs[imp.rhs]! + n) (fun x => x.push (eqs[imp.lhs]! + n))
      revgraph := revgraph.modify (eqs[imp.lhs]!) (fun x => x.push eqs[imp.rhs]!)
      revgraph := revgraph.modify (eqs[imp.lhs]! + n) (fun x => x.push (eqs[imp.rhs]! + n))
    | .nonimplication imp =>
      graph := graph.modify (eqs[imp.lhs]!) (fun x => x.push (eqs[imp.rhs]! + n))
      revgraph := revgraph.modify (eqs[imp.rhs]! + n) (fun x => x.push eqs[imp.lhs]!)

  let mut vis : Array Bool := Array.mkArray (2 * n) false
  let mut order : Array Nat := Array.mkEmpty (2 * n)

  -- compute SCCs and the condensation graph using Kosaraju's algorithm
  for i in [0:2*n] do
    unless vis[i]! do
      (vis, order) := dfs1 graph i vis order

  order := order.reverse

  let mut component : Array Nat := Array.mkArray (2 * n) 0
  let mut last_component : Nat := 0


  for i in order do
    if component[i]! == 0 then do
      last_component := last_component + 1
      component := dfs2 revgraph i component last_component

  let mut components : Array (Array Nat) := Array.mkArray last_component #[]
  let mut comp_graph : Array (Std.HashSet Nat) := Array.mkArray last_component {}

  for i in [0:2*n] do
    components := components.modify (component[i]!-1) (fun x ↦ x.push i)
    for j in graph[i]! do
      unless component[i]! == component[j]! do
        comp_graph := comp_graph.modify (component[i]!-1) (fun x ↦ x.insert (component[j]!-1))

  -- Run bitset transitive closure on the condensation graph
  let mut reachable : Array Bitset := Array.mkArray last_component (Bitset.mk last_component)

  for i_ in [0:last_component] do
    let i := last_component - 1 - i_
    reachable := reachable.modify i (fun x ↦ x.set i)
    for j in comp_graph[i]! do
      reachable := reachable.modify i (fun x ↦ x ||| reachable[j]!)

  -- extract the implications
  let mut ans : Array Edge := #[]

  for i in [:last_component] do
    for j in [:last_component] do
      if reachable[i]!.get j then
        for x in components[i]! do
          for y in components[j]! do
            if x == y then continue
            if x < n && y < n then
              ans := ans.push (.implication ⟨eqs_order[y]!, eqs_order[x]!⟩)
            else if x < n then
              ans := ans.push (.nonimplication ⟨eqs_order[x]!, eqs_order[y - n]!⟩)

  pure ans

def collectClosure {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (Std.HashMap Implication Outcome) := do
  let mut ans : Std.HashMap Implication Outcome := {}
  let thms := (← Result.extractTheorems).filterMap (EntryVariant.toEdge? ∘ Entry.variant)
  for thm in thms do
    ans := ans.insertIfNew thm.get (.explicit_theorem thm.isTrue)
  for imp_thm in closure thms do
    ans := ans.insertIfNew imp_thm.get (.implicit_theorem imp_thm.isTrue)
  let all := (← Result.extractEquationalResults).filterMap (EntryVariant.toEdge? ∘ Entry.variant)
  for thm in all do
    ans := ans.insertIfNew thm.get (.explicit_conjecture thm.isTrue)
  for imp_thm in closure all do
    ans := ans.insertIfNew imp_thm.get (.implicit_conjecture imp_thm.isTrue)

  return ans

/-- Prints the contents of the conjecture environment extension.
-/
syntax (name := printClosure) "#print_closure" : command

elab_rules : command
| `(command| #print_closure) => do
  let rs ← collectClosure
  for ⟨⟨lhs, rhs⟩, out⟩ in rs do
    println! "{lhs} → {rhs}: {out}"

syntax (name := checkClosure) "#check_closure" ident ident : command

elab_rules : command
| `(command| #check_closure $a $b) => do
  let rs ← collectClosure
  println! "{a} → {b}: {rs.getD ⟨a.getId.toString, b.getId.toString⟩ .unknown}"
  println! "{b} → {a}: {rs.getD ⟨b.getId.toString, a.getId.toString⟩ .unknown}"

end Closure
