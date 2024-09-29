import equational_theories.Result
import equational_theories.Conjecture

open Result

def Result.EntryVariant.lhs : EntryVariant → String
  | .nonimplication x | .implication x => x.lhs

def Result.EntryVariant.rhs : EntryVariant → String
  | .nonimplication x | .implication x => x.rhs

namespace Closure


partial def dfs1 (graph : Array (Array Nat)) (vertex : Nat) (vis : Array Bool) (order : Array Nat) :
    Id (Array Bool × Array Nat) := do
  let mut vis1 := vis.set! vertex true
  let mut ord := order
  for v in graph[vertex]! do
    unless vis1[v]! do
      (vis1, ord) ← dfs1 graph v vis1 ord
  pure (vis1, ord.push vertex)

partial def dfs2 (graph : Array (Array Nat)) (vertex : Nat) (component : Array Nat) (component_id : Nat) :
    Id (Array Nat) := do
  let mut comp := component.set! vertex component_id
  for v in graph[vertex]! do
    if component[v]! == 0 then
      comp := dfs2 graph v comp component_id
  pure comp

def Bitset := Array UInt64

instance : Inhabited Bitset := ⟨#[]⟩

def Bitset.mk (n : Nat) : Bitset := Array.mkArray ((n + 63) >>> 6) 0

def Bitset.set (b : Bitset) (n : Nat) : Bitset :=
  b.modify (n >>> 6) (fun x ↦ x ||| (1 <<< ((UInt64.ofNat n) &&& 63)))

instance : HOr Bitset Bitset Bitset where
  hOr a b := a.zipWith b (· ||| ·)

def closure (inp : Array EntryVariant) : IO (Array EntryVariant) := do

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
      revgraph := graph.modify (eqs[imp.rhs]! + n) (fun x => x.push eqs[imp.lhs]!)

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
      component := dfs2 graph i component last_component

  let mut components : Array (Array Nat) := Array.mkArray last_component #[]
  let mut comp_graph : Array (Std.HashSet Nat) := Array.mkArray last_component {}

  for i in [0:2*n] do
    components := components.modify (component[i]!-1) (fun x ↦ x.push i)
    for j in graph[i]! do
      unless component[i]! == component[j]! do
        comp_graph := comp_graph.modify (component[i]!-1) (fun x ↦ x.insert (component[j]!-1))

  IO.eprintln s!"{components}"

  -- Run bitset transitive closure on the condensation graph
  let mut reachable : Array Bitset := Array.mkArray last_component (Bitset.mk last_component)

  for i_ in [0:last_component] do
    let i := last_component - 1 - i_
    reachable := reachable.modify i (fun x ↦ x.set i)
    for j in comp_graph[i]! do
      reachable := reachable.modify i (fun x ↦ x ||| reachable[j]!)

  -- extract the implications
  let mut ans : Array EntryVariant := #[]

  for i in [:last_component] do
    for j in comp_graph[i]! do
      for x in components[i]! do
        for y in components[j]! do
          if x < n && y < n then
            ans := ans.push (.implication ⟨eqs_order[y]!, eqs_order[x]!⟩)
          else if x < n then
            ans := ans.push (.nonimplication ⟨eqs_order[x]!, eqs_order[y - n]!⟩)

  pure ans

/-- Prints the contents of the conjecture environment extension.
-/
syntax (name := printClosure) "#print_closure" : command

elab_rules : command
| `(command| #print_closure) => do
  let rs ← extractResults
  let rs' : Array EntryVariant ← closure (rs.map Entry.variant)
  for res in rs' do
    match res with
    | .implication ⟨lhs, rhs⟩ => println! "{lhs} → {rhs}"
    | .nonimplication ⟨lhs, rhs⟩ => println! "¬ ({lhs} → {rhs})"

end Closure
