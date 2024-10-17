import equational_theories.RArray
import equational_theories.MagmaLaw
import equational_theories.Equations.All

open Lean Elab

elab "defineLaws%" : term => do
  let consts : RArray Expr := RArray.ofFn (h := by omega) fun (⟨i, _⟩ : Fin 4694) =>
    mkConst (.mkSimple s!"Law{i+1}")
  return consts.toExpr (mkConst ``Law.NatMagmaLaw) id

def laws : RArray Law.NatMagmaLaw := defineLaws%

example : laws[1000] = Law1001 := rfl

/-!
The laws are in order, so we can use binary search to find it.

Unclear if this is fast enough to be used with kernel reduction to go
through all magmas.
-/

def FreeMagma.comp (m1 m2 : FreeMagma Nat) : Ordering :=
  if m1.forks < m2.forks then
    .lt
  else if m1.forks > m2.forks then
    .gt
  else match m1, m2 with
    | .Leaf n,     .Leaf m     => compare n m
    | .Leaf _,     .Fork _ _   => .lt
    | .Fork _ _,   .Leaf _     => .gt
    | .Fork l1 r1, .Fork l2 r2 => (l1.comp l2).then (r1.comp r2)

def Law.MagmaLaw.forks {α} (l : Law.MagmaLaw α) : Nat :=
  l.lhs.forks + l.rhs.forks

def Law.MagmaLaw.comp (l1 l2 : Law.NatMagmaLaw) : Ordering :=
  let l1' := l1.map (fun _ => 0)
  let l2' := l2.map (fun _ => 0)
  Ordering.then (compare l1.forks l2.forks) <|
  Ordering.then (FreeMagma.comp l1'.lhs l2'.lhs) <|
  Ordering.then (FreeMagma.comp l1'.rhs l2'.rhs) <|
  Ordering.then (FreeMagma.comp l1.lhs l2.lhs) <|
  (FreeMagma.comp l1.rhs l2.rhs)

def findMagmaLaw (l : Law.NatMagmaLaw) : Nat :=
  go 0 laws.size (laws.size+1) (by omega)
where
  go lb w fuel (hfuel : w < fuel) := match fuel with
    | 0 => by contradiction
    | fuel+1 =>
      if _ : w ≤ 1 then
        lb
      else
        let w' := w/2
        let mid := lb + w'
        let l' := laws[mid]
        if l.comp l' = .lt then
          go lb w' fuel (by omega)
        else
          go mid w' fuel (by omega)
  termination_by structural fuel

/-- Checks whether variables are canonically ordered -/
def FreeMagma.is_canonical (next : Nat) : FreeMagma Nat → Option Nat
  | .Leaf i => do
    guard (i ≤ next)
    if i = next then
      return next + 1
    else
      return next
  | .Fork l r => do
    let next' ← l.is_canonical next
    let next'' ← r.is_canonical next'
    return next''

def Law.MagmaLaw.is_canonical (l : Law.MagmaLaw Nat) : Bool :=
  ((l.lhs.is_canonical 0).bind (fun n => l.rhs.is_canonical n)).isSome

/--
This would be the compleness theorem.

But in order to prove this one probably has to define a verified generator
for canonical magmas up to a given size.
-/
theorem laws_complete :
  ∀ l : Law.MagmaLaw Nat, l.forks ≤ 4 → l.is_canonical →
  ∃ (i : Nat), l = laws[i] := by sorry
