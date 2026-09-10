import equational_theories.EndToEnd.Verified

/-!
# Human-readable output for `resolveImplication`
-/

namespace EndToEnd

def lawName (i : Nat) : String := s!"Law{i + 1}"

/-- The laws an implication passes through, starting at `n`. -/
def Implication.laws (pos : RArray PosFact) (n : Nat) (c : Implication) : List Nat :=
  n :: c.map fun k => (pos.get k).conc

/-- An implication rendered as `Law2 ⟹ Law3 ⟹ Law47`. An empty one is just `Law2` (reflexivity). -/
def Implication.render (pos : RArray PosFact) (n : Nat) (c : Implication) : String :=
  String.intercalate " ⟹ " ((Implication.laws pos n c).map lawName)

/-- Render whichever way the pair `(n, m)` resolved. -/
def renderResolution (C : Certificate) (pos : RArray PosFact) (neg : RArray NegFact)
    (n m : Nat) : String :=
  match resolveImplication C pos neg n m with
  | .inl c =>
      s!"{lawName n} ⟹ {lawName m}  (implied)\n" ++
      s!"  {c.length} step(s): {Implication.render pos n c}"
  | .inr r =>
      s!"{lawName n} ⊭ {lawName m}  (refuted)\n" ++
      s!"  witness #{r.fact} satisfies {lawName r.a} and refutes {lawName r.b}\n" ++
      s!"  {lawName r.a} ⟹ {lawName n}: {Implication.render pos r.a r.up}\n" ++
      s!"  {lawName m} ⟹ {lawName r.b}: {Implication.render pos m r.down}"

/-- `#eval printResolution 3 4065` -- law *numbers*, not the 0-based indices the theorems use. -/
def printResolution (n m : Nat) : IO Unit :=
  IO.println (renderResolution cert pos neg (n - 1) (m - 1))

end EndToEnd
