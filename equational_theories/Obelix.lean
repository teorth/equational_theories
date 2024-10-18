import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.DFinsupp.Notation
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Denumerable
import Mathlib.Tactic

import equational_theories.FactsSyntax
import equational_theories.EquationalResult
import equational_theories.Equations.Basic

-- The ``Obelix law''
-- equation 1491 := x = (y ◇ x) ◇ (y ◇ (y ◇ x))

namespace Obelix


--The particular group that we'll work on: (ℕ×ℕ)-indexed functions to ℤ with finite support.
--To ensure that this is computable (so that we can get the first few elements and verify
--that our non-Astericity), we use DFinsupp, the computable (and dependent) friend of Finsupp.
--The ℕ×ℕ lets us easily get "fresh" generators to keep extending the function. Finite support means
--that the group is still countable, so we can denumerate every element and eventually add it
--to the domain. We could easily use ℚ or Fin p instead of ℤ if we wanted.
--Significant amounts of the construction -- even defining the invariants of the partial function --
--depend on this, so we use it explicitly instead of making PartialSolution depend on a group G.
abbrev A : Type := Π₀ _ : ℕ × ℕ, ℤ

noncomputable instance A_group : AddCommGroup A := inferInstance

@[ext]
structure PartialSolution where
  --A partial solution is a function f : A → A satisfying certain invariants, with support Supp.
  Supp : Set A
  f : A → A
  --If x is in the domain, so is f(x).
  Closed_f : ∀ {a}, (ha : a ∈ Supp) → f a ∈ Supp
  --If x is in the domain, so is f (f x) - f(x).
  Closed_sub : ∀ {a}, (ha : a ∈ Supp) → f (f a) - f a ∈ Supp
  --For all x where it's defined, f( f(f(x)) - f(x) ) = x - f(x).
  Valid : ∀ {a}, (ha : a ∈ Supp) → f (f (f a) - f a) = a - f a
  --There are nats n and m such that...
  n : ℕ
  m : ℕ
  --the Supp is empty for any (a : A) with support on a (i,j) where i > n.
  noSuppN : ∀ (a : A), (∃ i j, n < i ∧ a (i,j) ≠ 0) → a ∉ Supp
  --and for n = i, it's empty whenever j > m.
  noSuppM : ∀ (a : A), (∃ j, m < j ∧ a (n,j) ≠ 0) → a ∉ Supp

namespace PartialSolution

/-- The bifurcation tree of new elements to add to solution, defined as a ℕ sequence of (x,f(x)) pairs.
The encoding is seq 0 for the root (a,·), and node i has children 2i+1 and 2i+2 for entries
 (f(x),·) and (f(f(x))-f(x),·) respectively.
-/
def bifurcationTree (f : PartialSolution) {a : A} (ha : a ∉ f.Supp) (n : ℕ) : A × A :=
  if n = 0 then
    (a, fun₀ | (f.n, f.m+n+1) => 1)
  else if Odd n then
    let i := (n-1)/2;
    let x := f.bifurcationTree ha i;
    (x.2, fun₀ | (f.n, f.m+n+1) => 1)
  else
    let i := (n-2)/2;
    let x := f.bifurcationTree ha i;
    let fx := f.bifurcationTree ha (n-1);
    (fx.2 - x.2, x.1 - x.2)

/-- The elements in the bifurcation tree do not overlap with the existing domain. -/
theorem bifurcationTreeDisjoint (f : PartialSolution) {a : A} (ha : a ∉ f.Supp) (n : ℕ) :
    (f.bifurcationTree ha n).1 ∉ f.Supp := by
  sorry

/-- The elements in the bifurcation tree do not overlap with the existing domain. -/
theorem bifurcationTreeDisjoint' (f : PartialSolution) {a b : A} (ha : a ∉ f.Supp)
    (hb : b ∈ f.Supp) : b ∉ Set.range (fun n ↦ (f.bifurcationTree ha n).1) :=
  fun ⟨n,hn⟩ ↦ f.bifurcationTreeDisjoint ha n ((by dsimp at hn; exact hn) ▸ hb)

/-- The elements in the bifurcation tree never have the same domain, the same fst. -/
theorem bifurcationTreeUnique (f : PartialSolution) {a : A} (ha : a ∉ f.Supp) (n₁ n₂ : ℕ) (hn : n₁ ≠ n₂) :
    (f.bifurcationTree ha n₁).1 ≠ (f.bifurcationTree ha n₂).1 := by
  sorry

open Classical in
/-- Extend a partial solution with an element not in its support, adding the full bifurcation tree. -/
noncomputable def add (f : PartialSolution) {x : A} (hx : x ∉ f.Supp) : PartialSolution where
  Supp := f.Supp ∪ Set.range (fun n ↦ (f.bifurcationTree hx n).1)
  f a := if h : a ∈ Set.range (fun n ↦ (f.bifurcationTree hx n).1) then
      (f.bifurcationTree hx (Nat.find h)).2
    else
      f.f a
  Closed_f := by
    rintro a (h|h)
    · apply Or.inl
      simp only [dif_neg (f.bifurcationTreeDisjoint' hx h)]
      exact f.Closed_f h
    · apply Or.inr
      obtain ⟨n,hn⟩ := h
      beta_reduce at hn
      simp
      rw [dif_pos ?_]
      use 2*n + 1
      sorry
      use n
  Closed_sub := by
    rintro a (h|h)
    · apply Or.inl
      simp only [dif_neg (f.bifurcationTreeDisjoint' hx h),
        dif_neg (f.bifurcationTreeDisjoint' hx  (f.Closed_f h))]
      exact f.Closed_sub h
    · apply Or.inr
      simp only [dif_pos h]
      obtain ⟨n,hn⟩ := h
      beta_reduce at hn
      use 2*n + 2
      simp only [Set.mem_range, exists_apply_eq_apply, ↓reduceDIte]
      sorry
  Valid := by
    sorry
  n := f.n+1
  m := 0
  noSuppN := by
    rintro a ⟨i,j,hi,ha⟩
    simp only [Set.mem_union, Set.mem_range, not_or, not_exists]
    constructor
    · exact f.noSuppN a ⟨i, j, by linarith, ha⟩
    · intro x
      sorry
  noSuppM := by
    rintro a ⟨j,hi,ha⟩
    simp only [Set.mem_union, Set.mem_range, not_or, not_exists]
    constructor
    · exact f.noSuppN a ⟨f.n+1, j, by linarith, ha⟩
    · intro x
      sorry

/-- The extended partial solution has the new element in the support. -/
theorem add_supp (f : PartialSolution) {x : A} (hx : x ∉ f.Supp) : x ∈ (f.add hx).Supp :=
  Or.inr ⟨0, by simp only [bifurcationTree, ↓reduceIte]⟩

/-- The extended partial solution includes the old support. -/
theorem extends_supp (f : PartialSolution) {x y : A} (hx : x ∉ f.Supp) (hy : y ∈ f.Supp) :
    y ∈ (f.add hx).Supp :=
  Or.inl hy

/-- The extended partial solution agrees with the old partial solution on its domain. -/
theorem agrees_supp (f : PartialSolution) {x y : A} (hx : x ∉ f.Supp) (hy : y ∈ f.Supp) :
    f.f y = (f.add hx).f y := by
  simp [add, dif_neg (f.bifurcationTreeDisjoint' hx hy)]

open Classical in
/-- Pick the next element to add, using a denumeration of everything in the group. -/
noncomputable def nextElemToAdd (f : PartialSolution) : {x : A // x ∉ f.Supp} := by
  have Pn : ∃ n : ℕ, ∃ x : {x : A // x ∉ f.Supp}, (Encodable.decode n) = some x := by
    obtain ⟨x,hx⟩ : ∃ x : A, x ∉ f.Supp :=
       ⟨fun₀ | (f.n+1, 0) => 1, f.noSuppN _ ⟨f.n+1, 0, by norm_num⟩⟩
    use Encodable.encode (α := {x : A // x ∉ f.Supp}) ⟨x, hx⟩, ⟨x, hx⟩
    exact Encodable.encodek _
  let k : Option {x : A // x ∉ f.Supp} := Encodable.decode (Nat.find Pn)
  use k.get ?_
  all_goals (
    obtain ⟨x, hx1⟩ := Nat.find_spec Pn
    simp [k, hx1, x.2]
  )

/-- Repeatedly extend f by the least element not in its domain, and the bifurcation tree that element
  generates. -/
noncomputable def closureSeq (f : PartialSolution) : ℕ → PartialSolution
| 0 => f
| n+1 => (closureSeq f n).add (closureSeq f n).nextElemToAdd.2

/-- All elements are eventually in the closure. -/
theorem closureSeq_eventually_total (f : PartialSolution) (x : A) :
    ∃n, x ∈ (f.closureSeq n).Supp := by
  sorry

open Classical in
/-- Make the linearizing function f from the closure. -/
noncomputable def closureLinear (f : PartialSolution) : A → A :=
  fun a ↦ (f.closureSeq (Nat.find (f.closureSeq_eventually_total a))).f a

/-- The linearizing function satisfies the functional equation, f( f(f(x)) - f(x) ) = x - f(x). -/
theorem closureLinear_funeq (f₀ : PartialSolution) :
    let f := closureLinear f₀; ∀ x, f (f (f x) - f x) = x - f x := by
  sorry

/-- The linearizing function agrees with the initial PartialSolution on its support. -/
theorem closureLinear_extends (f₀ : PartialSolution) :
    ∀ x, (h : x ∈ f₀.Supp) → closureLinear f₀ x = f₀.f x := by
  sorry

/-- Define the magma from the linearizing function. -/
noncomputable def closure (f : PartialSolution) : A → A → A :=
  fun a b ↦ a + (closureLinear f) (b - a)

/-- The resulting magma obeys the Obelix rule. -/
theorem closure_prop (f : PartialSolution) : ∀ x y,
    x = closure f (closure f y x) (closure f y (closure f y x)) :=
  fun x y ↦ by simp [closure, closureLinear_funeq f (x - y)]

/-- An initial solution, given by the empty partial function. -/
def initial : PartialSolution where
  Supp := ∅
  f _ := 0
  Closed_f ha := ha.elim
  Closed_sub ha := ha.elim
  Valid ha := ha.elim
  n := 0
  m := 0
  noSuppN _ _ := id
  noSuppM _ _ := id

/-- The first element to add to the empty solution is "0". -/
theorem nextElemToAdd_initial_zero : initial.nextElemToAdd = (0:A) := by
  unfold nextElemToAdd
  simp
  have : (fun a ↦ Classical.propDecidable (∃ x : { x // x ∉ initial.Supp },
      @Encodable.decode { x // x ∉ initial.Supp } (open Classical in Subtype.encodable) a = some x)) =
      (fun a ↦ Decidable.isTrue (by
        simp
      )) := by
    funext
    ext
  sorry

/--
--Pick two elements for the counterexample, x and y. We'll also need their difference.
-/
def x : A := 0
def y : A := fun₀ | (0, 1) => 1
def my : A := fun₀ | (0, 1) => -1
def z : A := fun₀ | (0, 6) => 1

open Classical

theorem x_sub_y_eq_my : x - y = my := by simp [x, y, my]

--We'll need to prove that they occur at positions 0 and 1, respectively, in order to get
--their values from f. No elements are at step 0 (empty function).
theorem none_in_initial : ∀ (z:A), ¬Nat.find (initial.closureSeq_eventually_total z) = 0 := by
  simp [Nat.find_eq_zero, initial, closure, closureSeq]

--x occurs at step 1 (first tree), at position 0. f(x) = y.
theorem h_pos_x : ((initial.closureSeq 0).bifurcationTree
    (closureSeq.proof_2 initial 0) 0) = (x,y) := by
  simpa [bifurcationTree, closureSeq, initial, y] using nextElemToAdd_initial_zero

theorem h_pos_my : ((initial.closureSeq 0).bifurcationTree
    (closureSeq.proof_2 initial 0) 5) = (my,z) := by
  simp [my, closureSeq, nextElemToAdd_initial_zero]
  native_decide

theorem h_find_x : Nat.find (initial.closureSeq_eventually_total x) = 1 := by
  suffices Nat.find (initial.closureSeq_eventually_total x) ≤ 1 by
    have := none_in_initial x; omega
  apply Nat.find_le
  apply Or.inr
  use 0
  simp [h_pos_x]

theorem h_find_my : Nat.find (initial.closureSeq_eventually_total my) = 1 := by
  suffices Nat.find (initial.closureSeq_eventually_total my) ≤ 1 by
    have := none_in_initial my; omega
  apply Nat.find_le
  apply Or.inr
  use 5
  simp [h_pos_my]

theorem h_fx_eq_y : initial.closureLinear x = y := by
  have : ((initial.closureSeq 0).bifurcationTree (closureSeq.proof_2 initial 0) 0).2 = y := by
    rw [h_pos_x]
  convert this
  let this : ∃ y, ((initial.closureSeq 0).bifurcationTree (closureSeq.proof_2 initial 0) y).1 = x := by
    use 0
    simp [h_pos_x]
  simp [closureLinear, add, h_find_x]
  rw [closureSeq, add]
  simp only [Set.mem_range, dif_pos this]
  simp only [closureSeq, nextElemToAdd_initial_zero]
  unfold this
  native_decide

theorem h_fmy_eq_z : initial.closureLinear my = z := by
  have : ((initial.closureSeq 0).bifurcationTree (closureSeq.proof_2 initial 0) 5).2 = z := by
    rw [h_pos_my]
  convert this
  let this : ∃ y, ((initial.closureSeq 0).bifurcationTree (closureSeq.proof_2 initial 0) y).1 = my := by
    use 5
    simp [h_pos_my]
  simp [closureLinear, add, h_find_my]
  rw [closureSeq, add]
  simp only [Set.mem_range, dif_pos this]
  simp only [closureSeq, nextElemToAdd_initial_zero]
  unfold this
  native_decide

#eval initial.bifurcationTree (show 0 ∉ ∅ from id) 5

open Classical in
-- @[equational_result]
theorem Equation1491_facts : ∃ (G : Type) (_ : Magma G), Facts G [1491] [65] := by
  use A, ⟨initial.closure⟩
  simp only [Equation1491, closure_prop, implies_true, not_forall, true_and]
  constructor
  · exact closure_prop initial
  · --Provide the data
    use x, y
    --y occurs at step 1 (first tree), at position 1.
    have h_pos_y : ((initial.closureSeq 0).bifurcationTree
        (closureSeq.proof_2 initial 0) 1).1 = y := by
      simp [bifurcationTree, closureSeq, initial]
    have h_find_y : Nat.find (initial.closureSeq_eventually_total y) = 1 := by
      suffices Nat.find (initial.closureSeq_eventually_total y) ≤ 1 by
        have := none_in_initial y; omega
      apply Nat.find_le
      apply Or.inr
      use 1
    --my occurs at step 1 (first tree), at position 5.
    have h_pos_my : ((initial.closureSeq 0).bifurcationTree
        (closureSeq.proof_2 initial 0) 5).1 = my := by
      simp [my, closureSeq, nextElemToAdd_initial_zero]
      native_decide
    have h_find_my : Nat.find (initial.closureSeq_eventually_total my) = 1 := by
      suffices Nat.find (initial.closureSeq_eventually_total my) ≤ 1 by
        have := none_in_initial my; omega
      apply Nat.find_le
      apply Or.inr
      use 5

    nth_rewrite 3 [closure]
    rw [x_sub_y_eq_my]
    unfold closureLinear
    -- unfold_let x y my at *
    -- clear x y my
    rw [h_find_my]
    -- unfold initial
    rw [← x_m_y_eq_my] at h_find_my
    simp [h_find_x, h_find_y, h_find_my]
    have := closureSeq.eq_def initial 0
    set i₀ := initial.bifurcationTree (show 0 ∉ ∅ from id) 0 with hi₀
    set i₁ := initial.bifurcationTree (show 0 ∉ ∅ from id) 1 with hi₁
    set i₂ := initial.bifurcationTree (show 0 ∉ ∅ from id) 2 with hi₂
    simp [initial, bifurcationTree, ← Nat.not_even_iff_odd] at hi₀ hi₁ hi₂
    sorry
