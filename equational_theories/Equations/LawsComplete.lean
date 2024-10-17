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
          go mid (w-w') fuel (by omega)
  termination_by structural fuel

def FreeMagma.max : FreeMagma Nat → Nat
  | .Leaf i => i
  | .Fork l r => Nat.max l.max r.max

def Law.MagmaLaw.max (l : Law.MagmaLaw Nat) : Nat := Nat.max l.lhs.max l.rhs.max

/-- Checks whether variables are canonically ordered -/
def FreeMagma.is_canonical (next : Nat) : FreeMagma Nat → Option Nat
  | .Leaf i => do
    if i < next then
      return next
    else if i = next then
      return next + 1
    else
      none
  | .Fork l r => do
    let next' ← l.is_canonical next
    let next'' ← r.is_canonical next'
    return next''

/-- Canonically reorders variables -/
def FreeMagma.canonicalize (m : FreeMagma Nat) : FreeMagma Nat :=
  ((go m).run #[]).run.1
where
  go : FreeMagma Nat → StateM (Array Nat) (FreeMagma Nat)
  | .Leaf v => do
    let xs ← get
    match xs.indexOf? v with
    | some i => return .Leaf i
    | none =>
      set (xs.push v)
      return .Leaf xs.size
  | .Fork l r => do
    let l ← go l
    let r ← go r
    return .Fork l r

def Law.MagmaLaw.canonicalize (l : Law.MagmaLaw Nat) : Law.MagmaLaw Nat :=
  (go.run #[]).run.1
where
  go : StateM (Array Nat) Law.NatMagmaLaw := do
    let lhs' ← FreeMagma.canonicalize.go l.lhs
    let rhs' ← FreeMagma.canonicalize.go l.rhs
    return ⟨lhs', rhs'⟩

theorem FreeMagma.canonicalize_is_canonical (m : FreeMagma Nat) (xs : Array Nat) :
  (FreeMagma.canonicalize.go m xs).run.1.is_canonical xs.size = some (FreeMagma.canonicalize.go m xs).run.2.size := by
  induction m generalizing xs with
  | Leaf v =>
    simp only [Id.run, canonicalize.go, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, set]
    cases xs.indexOf? v
    case none =>
      simp [StateT.bind, pure, StateT.pure, set, StateT.set, is_canonical]
    case some =>
      simp [StateT.bind, pure, StateT.pure, set, StateT.set, is_canonical]
  | Fork l r ih1 ih2 =>
    specialize ih1 xs
    specialize ih2 (canonicalize.go l xs).2
    simp_all [canonicalize.go, bind, StateT.run, Id.run, StateT.bind, pure, StateT.pure, set, StateT.set, is_canonical,
      bind, StateT.bind]
    rfl

def Law.MagmaLaw.is_canonical (l : Law.MagmaLaw Nat) : Bool :=
  ((l.lhs.is_canonical 0).bind (fun n => l.rhs.is_canonical n)).isSome &&
  (l.lhs.comp l.rhs = .lt || l.lhs = .Leaf 0) &&
  !(l.symm.canonicalize.comp l = .lt)

/-
A decision procedure for checking a predicate for all canonical magma laws of a certain size.
-/
def testVars (n : Nat) (P : Nat → Nat → Bool) :=
  (List.range n).all (fun i => P n i) && P (n+1) n

def testAllSplits (s : Nat) (P : Nat → Nat → Bool) : Bool :=
  (List.range (s+1)).all fun s' => P s' (s-s')

def testFreeMagmas (s n : Nat) (P : Nat → FreeMagma Nat → Bool) :=
  match s with
  | 0 =>
    testVars n fun n' i => P n' (.Leaf i)
  | s+1 =>
    testAllSplits s fun s1 s2 =>
      assert! s1 + s2 = s
      testFreeMagmas s1 n fun n' l =>
        testFreeMagmas s2 n' fun n'' r =>
          P n'' (.Fork l r)

def testLaws (s : Nat) (P : Law.NatMagmaLaw → Bool) :=
  testAllSplits s fun s1 s2 =>
      testFreeMagmas s1 0 fun n' l =>
        testFreeMagmas s2 n' fun _ r =>
          if l = .Leaf 0 || l.comp r = .lt then
            let law := ⟨l, r⟩
            if law.symm.canonicalize.comp law = .lt then
              true
            else
              P law
          else
            true

/-- info: true -/
#guard_msgs in
#eval testLaws 2 (fun l => l.forks = 2 ∧ l.is_canonical)

/-- info: true -/
#guard_msgs in
#eval testLaws 4 (fun l => l.forks = 4 ∧ l.is_canonical)

/--
This would be the compleness theorem.

But in order to prove this one probably has to define a verified generator
for canonical magmas up to a given size.
-/
theorem laws_complete :
  ∀ l : Law.MagmaLaw Nat, l.forks ≤ 4 → l.is_canonical →
  ∃ (i : Nat), l = laws[i] := by sorry

-- TODO: Prove that testLaw tests all laws. Until then:

/-- info: true -/
#guard_msgs in
#eval (List.range 5).all fun i => testLaws i fun l =>
  laws[findMagmaLaw l] = l
