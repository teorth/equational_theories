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
All the separate `Law{n}` definitions in one data structure.

```
example : laws[1000] = Law1001 := rfl
```
-/
def laws : RArray Law.NatMagmaLaw := defineLaws%

theorem laws.wf : laws.WF := by decide

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
  go 0 laws.size
where
  go lb w :=
    if w ≤ 1 then
      lb
    else
      let w' := w/2
      let mid := lb + w'
      let l' := laws[mid]
      if l.comp l' = .lt then
        go lb w'
      else
        go mid (w-w')

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
def FreeMagma.isCanonical (next : Nat) : FreeMagma Nat → Option Nat
  | .Leaf i => do
    if i < next then
      return next
    else if i = next then
      return next + 1
    else
      none
  | .Fork l r => do
    let next' ← l.isCanonical next
    let next'' ← r.isCanonical next'
    return next''

/--
Checks whether a magma law is canonical:
* Variables are canonically labeled
* `lhs < rhs` (with the exception of `0 ≃ 0`)
* The symmetric law did not come first
-/
def Law.MagmaLaw.isCanonical (l : Law.MagmaLaw Nat) : Bool :=
  ((l.lhs.isCanonical 0).bind (fun n => l.rhs.isCanonical n)).isSome &&
  (l.lhs.comp l.rhs = .lt || l.lhs = .Leaf 0) &&
  !(l.symm.canonicalize.comp l = .lt)

theorem FreeMagma.canonicalize_isCanonical (m : FreeMagma Nat) (xs : Array Nat) :
    (FreeMagma.canonicalize.go m xs).run.1.isCanonical xs.size =
    some (FreeMagma.canonicalize.go m xs).run.2.size := by
  induction m generalizing xs with
  | Leaf v =>
    simp only [Id.run, canonicalize.go, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, set]
    cases xs.indexOf? v
    case none =>
      simp [StateT.bind, pure, StateT.pure, set, StateT.set, isCanonical]
    case some =>
      simp [StateT.bind, pure, StateT.pure, set, StateT.set, isCanonical]
  | Fork l r ih1 ih2 =>
    specialize ih1 xs
    specialize ih2 (canonicalize.go l xs).2
    simp_all only [Id.run, isCanonical, bind, pure, Option.bind_some, Option.some_bind,
      canonicalize.go, StateT.bind, StateT.pure, Option.some.injEq]
    rfl

/-!
A decision procedure for checking a predicate for all canonical magma laws of a certain size.

The proofs are rather unpretty; maybe phrasing everything in terms of `Decidable` would
have made that easier. But what works works.
-/

open Lean Qq

def TestNat (n : Nat) (P : Nat → Prop) : Prop := ∀ i < n, P i

theorem TestNat.zero {P} : TestNat 0 P := by simp [TestNat]
theorem TestNat.succ {n P} (h1 : TestNat n P) (h2 : P n) : TestNat (n+1) P := by
  simpa only [TestNat, Nat.lt_succ_iff_lt_or_eq, or_imp, forall_and, forall_eq, and_true, h2]

def proveTestNat (n : Nat) {P : Q(Nat → Prop)} (hP : (i : Nat) → MetaM Q($P $i)) :
    MetaM Q(TestNat $n $P) := do
  match n with
  | 0 => pure q(TestNat.zero)
  | n+1 => pure q(TestNat.succ $(← proveTestNat n hP) $(← hP n))

def TestAllSplits (n : Nat) (P : Nat → Nat → Prop) : Prop := ∀ i j, i + j = n → P i j
def TestAllSplits' (i j : Nat) (P : Nat → Nat → Prop) : Prop :=
  ∀ i' < i, P i' (j + (i - i'))

theorem TestAllSplits'.zero {n P} : TestAllSplits' 0 n P := by simp [TestAllSplits', *]
theorem TestAllSplits'.succ {i j P}
    (h1 : TestAllSplits' i (j+1) P) (h2 : P i (j+1)) : TestAllSplits' (i+1) j P := by
  simp only [TestAllSplits', Nat.lt_succ_iff_lt_or_eq, or_imp, forall_and, forall_eq,
    Nat.add_sub_cancel_left] at *
  exact ⟨fun i' h => by convert h1 i' h using 1; omega, h2⟩

theorem TestAllSplits.start {n P} (h1 : TestAllSplits' n 0 P) (h2 : P n 0) : TestAllSplits n P := by
  have : ∀ i ≤ n, P i (n - i) := by
    simpa [TestAllSplits', Nat.le_iff_lt_or_eq, or_imp, forall_and, h2] using h1
  intro i j eq
  cases Nat.eq_sub_of_add_eq' eq
  exact this _ (by omega)

def proveTestAllSplits (n : Nat) {P : Q(Nat → Nat → Prop)} (hP : (i j : Nat) → MetaM Q($P $i $j)) :
    MetaM Q(TestAllSplits $n $P) := do
  let rec go (i j : Nat) : MetaM Q(TestAllSplits' $i $j $P) := do
    match i with
    | 0 => pure q(TestAllSplits'.zero)
    | i + 1 => pure q(TestAllSplits'.succ $(← go i (j+1)) $(← hP i (j+1)))
  pure q(TestAllSplits.start $(← go n 0) $(← hP n 0))

def TestFreeMagmas (s n : Nat) (P : Nat → FreeMagma Nat → Prop) :=
  ∀ m n', m.forks = s → m.isCanonical n = some n' → P n' m

theorem TestFreeMagmas.zero {n P}
    (H : TestNat (n+1) fun i => P (if i < n then n else n+1) (.Leaf i))
    : TestFreeMagmas 0 n P := by
  intro
  | .Leaf i, n, _, eq =>
    simp (config := {contextual := true}) [TestFreeMagmas, TestNat, FreeMagma.isCanonical] at *
    specialize H i
    split at eq
    · simp_all; apply H; omega
    · split at eq <;> simp_all

theorem TestFreeMagmas.succ {s n P}
    (H : TestAllSplits s fun s1 s2 =>
      TestFreeMagmas s1 n fun n l =>
        TestFreeMagmas s2 n fun n r =>
          P n (.Fork l r))
    : TestFreeMagmas (s+1) n P := by
  intro
  | .Fork l r, n, hadd =>
    simp (config := {contextual := true}) [TestFreeMagmas, FreeMagma.isCanonical,
        TestAllSplits, Option.bind_eq_some, FreeMagma.forks] at *
    rintro n'' hcan1
    exact H _ _ hadd _ _ rfl hcan1 _ _ rfl

partial def proveTestFreeMagmas (s n : Nat) (P : Q(Nat → FreeMagma Nat → Prop))
    (hP : (i : Nat) → FreeMagma Nat → (m : Q(FreeMagma Nat)) → MetaM Q($P $i $m)) :
    MetaM Q(TestFreeMagmas $s $n $P) := do
  match s with
  | 0 =>
    let h ← proveTestNat (n+1) fun i : Nat => hP (if i < n then n else n+1) (.Leaf i) q(.Leaf $i)
    pure q(TestFreeMagmas.zero $h)
  | s + 1 =>
    let h ← proveTestAllSplits s fun s1 s2 : Nat =>
      proveTestFreeMagmas s1 n q(fun n l => TestFreeMagmas $s2 n fun n r => $P n (.Fork l r))
        fun n l l' => proveTestFreeMagmas s2 n q(fun n r => $P n (.Fork $l' r))
          fun n r r' => hP n (.Fork l r) q(.Fork $l' $r')
    pure q(TestFreeMagmas.succ $h)

def TestLawsBody (l r : FreeMagma Nat) (P : Law.NatMagmaLaw → Prop) :=
  (l ≠ Lf 0 → l.comp r = Ordering.lt) →
  ¬(l ≃ r).symm.canonicalize.comp (l ≃ r) = .lt → P (l ≃ r)

theorem TestLawsBody.mk1 {l r P}
    (H : (l ≃ r).symm.canonicalize.comp (l ≃ r) = .lt) : TestLawsBody l r P :=
  fun _ h => h.elim H

theorem TestLawsBody.mk2 {l r P} (H : P (l ≃ r)) : TestLawsBody l r P :=
  fun _ _ => H

theorem TestLawsBody.mk3 {l r P}
    (h1 : decide (l = Lf 0) = false) (h2 : decide (l.comp r = .lt) = false) :
    TestLawsBody l r P :=
  fun h => by simp at h1 h2; cases h2 (h h1)

partial def proveTestLawsBody (l r : FreeMagma Nat) (l' r' : Q(FreeMagma Nat))
    (P : Q(Law.NatMagmaLaw → Prop))
    (hP : (l : Law.NatMagmaLaw) → (l : Q(Law.NatMagmaLaw)) → MetaM Q($P $l)) :
    MetaM Q(TestLawsBody $l' $r' $P) := do
  if l = .Leaf 0 || l.comp r = .lt then
    let law := (l ≃ r)
    if law.symm.canonicalize.comp law = .lt then
      let e : Q(($l' ≃ $r').symm.canonicalize.comp ($l' ≃ $r') = .lt) := (q(Eq.refl Ordering.lt) :)
      pure q(TestLawsBody.mk1 $e)
    else
      pure q(TestLawsBody.mk2 $(← hP law q($l' ≃ $r')))
  else
    let h1 : Q(decide ($l' = Lf 0) = false) := (q(Eq.refl false) :)
    let h2 : Q(decide (($l').comp $r' = .lt) = false) := (q(Eq.refl false) :)
    pure q(TestLawsBody.mk3 $h1 $h2)

def TestLaws (s : Nat) (P : Law.NatMagmaLaw → Prop) :=
  ∀ l : Law.MagmaLaw Nat, l.forks = s → l.isCanonical → P l

theorem TestLaws.mk {s P}
    (H : TestAllSplits s fun s1 s2 =>
    TestFreeMagmas s1 0 fun n l =>
      TestFreeMagmas s2 n fun _ r =>
        TestLawsBody l r P)
    : TestLaws s P := by
  unfold TestLaws
  simp [TestAllSplits, TestFreeMagmas] at *
  rintro ⟨l, r⟩ hs hcan
  simp [Law.MagmaLaw.isCanonical, Option.isSome_iff_exists, Option.bind_eq_some] at hcan
  obtain ⟨⟨⟨n'', n', hcan1, hcan2⟩, hcomp⟩, hsymm⟩ := hcan
  exact H _ _ hs _ _ rfl hcan1 _ _ rfl hcan2 hcomp.resolve_right hsymm

partial def proveTestLaws (s : Nat) (P : Q(Law.NatMagmaLaw → Prop))
    (hP : Law.NatMagmaLaw → (m : Q(Law.NatMagmaLaw)) → MetaM Q($P $m)) :
    MetaM Q(TestLaws $s $P) := do
  let h ← proveTestAllSplits s fun s1 s2 : Nat =>
    proveTestFreeMagmas s1 0 q(fun n l => TestFreeMagmas $s2 n fun _ r => TestLawsBody l r $P)
      fun n l l' => proveTestFreeMagmas s2 n q(fun _ r => TestLawsBody $l' r $P)
        fun _ r r' => proveTestLawsBody l r l' r' P hP
  pure q(TestLaws.mk $h)

def TestLawsUpto (s : Nat) (P : Law.NatMagmaLaw → Prop) :=
  ∀ l : Law.MagmaLaw Nat, l.forks ≤ s → l.isCanonical → P l

theorem TestLawsUpto.mk {s P}
    (H : TestNat (s+1) fun s' => TestLaws s' P)
    : TestLawsUpto s P := by
  simp [TestLawsUpto, TestLaws, TestNat, Nat.lt_succ_iff] at *
  intro i his hcanon
  exact H _ his _ rfl hcanon

partial def proveTestLawsUpto (s : Nat) (P : Q(Law.NatMagmaLaw → Prop))
    (hP : Law.NatMagmaLaw → (m : Q(Law.NatMagmaLaw)) → MetaM Q($P $m)) :
    MetaM Q(TestLawsUpto $s $P) := do
  let h ← proveTestNat (s+1) fun s' : Nat => proveTestLaws s' P hP
  pure q(TestLawsUpto.mk $h)

/--
This theorem demonstrates that `laws`, the list of laws considered in this project, indeed
contains all (canonically represented) magma laws up to 4 operations.
-/
theorem laws_complete :
    ∀ l : Law.MagmaLaw Nat, l.forks ≤ 4 → l.isCanonical → ∃ (i : Nat), laws[i] = l :=
  by_elab proveTestLawsUpto 4 q(fun l => ∃ i : Nat, laws[i] = l) fun l l' => do
    let i : Nat := findMagmaLaw l
    let h : Q(laws[$i] = $l') := (q(Eq.refl $l') :)
    pure q(⟨$i, $h⟩)
