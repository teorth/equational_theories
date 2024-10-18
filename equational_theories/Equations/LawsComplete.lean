import equational_theories.RArray
import equational_theories.MagmaLaw
import equational_theories.Equations.All

/-!
This module proves that are actually looking at at the laws we claim to be looking at.

See `laws_complete` for the main result.
-/


open Lean Elab in
/--
An elaborator to assemble all the separate `Law{n}` definitions into one data structure.
-/
elab "defineLaws%" : term => do
  let consts : RArray Expr := RArray.ofFn (h := by omega) fun (⟨i, _⟩ : Fin 4694) =>
    mkConst (.mkSimple s!"Law{i+1}")
  return consts.toExpr (mkConst ``Law.NatMagmaLaw) id

/--
All the separte `Law{n}` definitions in one data structure.

```
example : laws[1000] = Law1001 := rfl
```
-/
def laws : RArray Law.NatMagmaLaw := defineLaws%

example : laws[1000] = Law1001 := rfl

/-!
The laws are in order, so we can use binary search to find it.
-/


/-- An ordering on `FreeMagma` that coincides with the order we put the laws in.  -/
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

/-- The number of forks in a magma law. -/
def Law.MagmaLaw.forks {α} (l : Law.MagmaLaw α) : Nat :=
  l.lhs.forks + l.rhs.forks

/-- An ordering on `NatMagmaLaw` that coincides with the order we put the laws in.  -/
def Law.MagmaLaw.comp (l1 l2 : Law.NatMagmaLaw) : Ordering :=
  let l1' := l1.map (fun _ => 0)
  let l2' := l2.map (fun _ => 0)
  Ordering.then (compare l1.forks l2.forks) <|
  Ordering.then (FreeMagma.comp l1'.lhs l2'.lhs) <|
  Ordering.then (FreeMagma.comp l1'.rhs l2'.rhs) <|
  Ordering.then (FreeMagma.comp l1.lhs l2.lhs) <|
  (FreeMagma.comp l1.rhs l2.rhs)

/--
Binary search on `laws` for a given law. If the given law is not in `laws`, an arbitrary value is
returned.
-/
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

/-- The largest used variable. -/
def FreeMagma.max : FreeMagma Nat → Nat
  | .Leaf i => i
  | .Fork l r => Nat.max l.max r.max

/-- The largest used variable. -/
def Law.MagmaLaw.max (l : Law.MagmaLaw Nat) : Nat := Nat.max l.lhs.max l.rhs.max

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

/-- Canonically reorders variables -/
def Law.MagmaLaw.canonicalize (l : Law.MagmaLaw Nat) : Law.MagmaLaw Nat :=
  (go.run #[]).run.1
where
  go : StateM (Array Nat) Law.NatMagmaLaw := do
    let lhs' ← FreeMagma.canonicalize.go l.lhs
    let rhs' ← FreeMagma.canonicalize.go l.rhs
    return ⟨lhs', rhs'⟩

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

/--
Checks whether a magma law is canonical:
* Variables are canonically labeled
* `lhs < rhs` (with the exception of `0 ≃ 0`)
* The symetric law did not come first
-/
def Law.MagmaLaw.is_canonical (l : Law.MagmaLaw Nat) : Bool :=
  ((l.lhs.is_canonical 0).bind (fun n => l.rhs.is_canonical n)).isSome &&
  (l.lhs.comp l.rhs = .lt || l.lhs = .Leaf 0) &&
  !(l.symm.canonicalize.comp l = .lt)

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

/-!
A decision procedure for checking a predicate for all canonical magma laws of a certain size.

The proofs are rather unpretty; maybe phrasing everything in terms of `Decidable` would
have made that easier. But what works works.
-/

def testNat : Nat → (P : Nat → Bool) → Bool
  | 0, _   => true
  | n+1, P => P n && testNat n P

def testAllSplits (s : Nat) (P : Nat → Nat → Bool) : Bool :=
  testNat (s+1) fun s' => P s' (s-s')

def testFreeMagmas (s n : Nat) (P : Nat → FreeMagma Nat → Bool) :=
  match s with
  | 0 =>
    testNat (n+1) fun i =>
      P (if i < n then n else n+1) (.Leaf i)
  | s+1 =>
    testAllSplits s fun s1 s2 =>
      assert! s1 + s2 = s -- Cunning trick to ensure termination!
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

def testLawsUpto (s : Nat) (P : Law.NatMagmaLaw → Bool) :=
  testNat (s+1) fun s' => testLaws s' P

/-- info: true -/
#guard_msgs in
#eval testLaws 2 (fun l => l.forks = 2 ∧ l.is_canonical)

/-- info: true -/
#guard_msgs in
#eval testLaws 4 (fun l => l.forks = 4 ∧ l.is_canonical)

@[simp]
theorem FreeMagmas.forks_eq_0_iff (m : FreeMagma Nat) :
  m.forks = 0 ↔ ∃ v, m = .Leaf v := by cases m <;> simp [FreeMagma.forks]

@[simp]
theorem FreeMagmas.forks_eq_succ_iff (m : FreeMagma Nat) n :
    m.forks = n+1 ↔ ∃ l r, m = .Fork l r ∧ l.forks + r.forks = n := by
  cases m
  case Leaf => simp [FreeMagma.forks]
  case Fork l r =>
    simp [FreeMagma.forks]
    constructor
    · intro h; use l, r
    · rintro ⟨_, _, ⟨rfl, rfl⟩, _⟩; assumption

theorem testNat_spec (n : Nat) P :
    testNat n P = true ↔ ∀ i < n, P i := by
  induction n
  next => simp [testNat]
  next n ih =>
    simp_all [testNat, Nat.lt_succ_iff_lt_or_eq]; clear ih
    constructor
    · rintro ⟨h1,h2⟩ i ⟨h2|h3⟩
      · apply h2 i (Nat.lt_add_one i)
      · apply h2 i (Nat.lt_succ_of_lt h3)
      · subst i; assumption
    · intro h
      constructor
      · apply h; right; rfl
      · intro i h2; apply h; left; assumption

theorem testAllSplits_spec (n : Nat) P :
    testAllSplits n P = true ↔ ∀ s1 s2, s1 + s2 = n → P s1 s2 := by
  rw [testAllSplits, testNat_spec]
  constructor
  · intro h s1 s2 hs12
    convert h s1 ?lt <;> omega
  · intro h i hlt
    apply h
    omega

theorem testFreeMagmas_spec (s n : Nat) P :
  testFreeMagmas s n P = true ↔ ∀ m n', m.forks = s → m.is_canonical n = some n' → P n' m = true := by
  induction s, n, P using testFreeMagmas.induct
  next n P =>
    simp (config := {contextual := true}) [testFreeMagmas, testNat_spec, FreeMagma.is_canonical]
    constructor
    · intro h
      rintro _ n' i rfl heq
      specialize h i
      split at heq
      next hlt => simp_all; apply h; omega
      next =>
        split at heq
        next => simp_all
        next  => simp_all
    · intro h i hi
      apply h _ _ _ rfl
      split <;> simp
      omega
  next n P s ih2 ih1 =>
    simp (config := {contextual := true}) [testFreeMagmas, FreeMagma.is_canonical,
      testAllSplits_spec, Option.bind_eq_some]
    constructor
    · rintro h _ n' l r rfl hadd n'' hcan1 hcan2
      specialize h _ _ hadd
      specialize ih1 _ _ hadd
      specialize ih2 _ _ hadd
      dsimp at *
      apply (ih2 _ l).mp _ _ _ rfl hcan2
      apply ih1.mp h _ _ rfl hcan1
    · intro h s1 s2 hadd
      specialize ih1 _ _ hadd
      specialize ih2 _ _ hadd
      rw [ih1]
      intro l n' hl hcan1
      rw [ih2]
      intro r n'' hr hcan2
      apply h _ n'' l r rfl (by simp [*])
      apply hcan1
      apply hcan2

theorem testLaws_spec (s : Nat) P :
  testLaws s P = true ↔ ∀ l : Law.MagmaLaw Nat, l.forks = s → l.is_canonical → P l = true := by
  unfold testLaws
  simp [testAllSplits_spec, testFreeMagmas_spec, Decidable.or_iff_not_imp_left]
  constructor
  · rintro h ⟨l, r⟩ hs hcan
    simp [Law.MagmaLaw.is_canonical] at hcan
    obtain ⟨⟨hcan, hcomp⟩, hsymm⟩ := hcan
    cases hcan1 : (FreeMagma.is_canonical 0 l)
    case none => simp [hcan1] at hcan
    case some n' =>
      cases hcan2 : (FreeMagma.is_canonical n' r)
      case none => simp [hcan1, hcan2] at hcan
      case some n'' =>
        apply h l.forks r.forks hs l _ rfl hcan1 _ _ rfl hcan2
        · intro hnLf0; simp_all
        · assumption
  · rintro h s1 s2 hs12 l n' hl hcan1 r n'' hr hcan2 hcomp hsymm
    apply h
    · simp [Law.MagmaLaw.forks, hs12, hl, hr]
    · simp [Law.MagmaLaw.is_canonical, hcan1, hcan2, hsymm]
      tauto

theorem testLawsUpto_spec (s : Nat) P :
    testLawsUpto s P = true ↔ ∀ l : Law.MagmaLaw Nat, l.forks ≤ s → l.is_canonical → P l = true := by
  simp [testLawsUpto, testLaws_spec, testNat_spec, Nat.lt_succ_iff]
  constructor
  · intro h i his hcanon
    apply h _ his _ rfl hcanon
  · rintro h i his l rfl hcanon
    apply h _ his hcanon

/--
Here we do the actual computation. For now using `native_decide`, more serious
engineering is necessary if we insist on using `by decide` here.
-/
theorem testLawsUpto4_computation :
  testLawsUpto 4 (fun l => laws[findMagmaLaw l] = l) = true := by native_decide

theorem laws_complete' :
    ∀ l : Law.MagmaLaw Nat, l.forks ≤ 4 → l.is_canonical → laws[findMagmaLaw l] = l := by
  simpa [decide_eq_true_eq]
    using (testLawsUpto_spec 4 (fun l => laws[findMagmaLaw l] = l)).mp testLawsUpto4_computation

/--
This theorem demonstrates that `laws`, the list of laws considered in this project, indeed
contains all (canonically represented) magma laws up to 4 operations.
-/
theorem laws_complete :
    ∀ l : Law.MagmaLaw Nat, l.forks ≤ 4 → l.is_canonical → ∃ (i : Nat), laws[i] = l :=
  fun l hl hcan => ⟨findMagmaLaw l, laws_complete' l hl hcan⟩
