-- This file mechanizes the construction described in:
-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/713.2C.201289.2C.201447/near/482236139
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Topology.Instances.AddCircle
import equational_theories.EquationalResult
import equational_theories.Equations.All

namespace Equation1447

section Construction
universe u

-- Select a surjective map `S : M → M` as the candidate squaring map
variable {M : Type u} (S : M → M) (hsurj : Function.Surjective S)

include hsurj

-- with the property that S, S^2, S^3 have no fixed points
def no_fixed_points : Prop := ∀ (m : M), S m ≠ m ∧ S (S m) ≠ m ∧ S (S (S m)) ≠ m

variable (hnofix : no_fixed_points S)
include hnofix

def square_roots (x : M) : Set M := { y : M | S y = x }

notation "√" => square_roots

omit hsurj hnofix in
lemma square_roots_elem_iff_square_root (x y : M) :
  y ∈ square_roots S x ↔ S y = x := by exact Set.mem_def

-- Thus, every element `x ∈ M` has a non-empty set of square roots
omit hnofix in
theorem non_empty_square_roots (x : M) : square_roots S x ≠ ∅ :=  by
  simp [square_roots,Set.eq_empty_iff_forall_not_mem]
  apply hsurj

omit hnofix in
theorem nonempty_square_roots ( x : M) : (square_roots S x).Nonempty :=  by
  rw [Set.nonempty_iff_ne_empty]
  exact (non_empty_square_roots S hsurj x)

-- which is disjoint from both `x` and `S x`.
omit hsurj in
theorem elem_notin_square (x : M) : x ∉ square_roots S x := by
  exact (hnofix x).1

omit hsurj in
theorem s_elem_notin_square (x : M) : S x ∉ square_roots S x := by
  exact (hnofix x).2.1

-- One can think of `S x` as the "parent" of `x`, and the elements of √`x`
-- ​ as "siblings" to each other, and "children" of `x`.
def parent (x : M) (y : M) : Prop := y = S x
def sibling (x : M) (y : M) : Prop := ∃ (z : M), x ∈ square_roots S z ∧ y ∈ square_roots S z
def child (x : M) (y : M) : Prop := x ∈ square_roots S y

variable  [DecidableEq M]

noncomputable def arbitraryRoot (x : M) : M :=
  Exists.choose (nonempty_square_roots S hsurj x)

omit hnofix [DecidableEq M] in
theorem arbitraryRoot_root (x : M) : arbitraryRoot S hsurj x ∈ square_roots S x :=
  Exists.choose_spec (α := M) (p := fun y => y ∈ square_roots S x) (nonempty_square_roots S hsurj x)

-- Define `x⋄y` to equal `S x` if `S x = S y` or `x = S y`; equal to `S y` if `x = S^2 y`; and equal to an arbitrary square root in `x`
-- ​ otherwise.
noncomputable def magmaOp : M → M → M := fun x y =>
  if S x = S y then S x else
  if x = S y then S x else
  if x = S (S y) then S y
  else arbitraryRoot S hsurj x

noncomputable instance instMagma : Magma M where
  op := magmaOp S hsurj

-- Observe that `x ⋄ y` is either the square of `x` or a square root of `x`,
-- with the former possibility occurring if and only if `S x = S y` or `x = S y`
-- (i.e. `x` is a parent or sibling of `y`).
theorem square_iff_eq (x y : M) :
 Magma.op (self:= instMagma S hsurj) x y = S x
 ↔ (S x = S y ∨ x = S y) := by
   simp only [Magma.op, magmaOp]
   constructor
   · case mp =>
      split_ifs
      · case pos h => intro _; left; exact h
      · case pos h => intro _; right; exact h
      · case pos h => intro h'; left; exact h'.symm
      · case neg h1 h2 h3 =>
          intro hcontra
          exfalso
          have hnotin := s_elem_notin_square S hnofix x
          rw [← hcontra] at hnotin
          apply hnotin
          exact arbitraryRoot_root S hsurj x
   · case mpr =>
      intro h
      cases h <;> split_ifs <;> aesop

theorem square_root_iff_neq (x y : M) :
 Magma.op (self:= instMagma S hsurj) x y ∈ square_roots S x
 ↔ ¬(S x = S y ∨ x = S y) := by
   simp only [Magma.op, magmaOp]
   constructor
   · case mp =>
      have hnot := s_elem_notin_square S hnofix x
      split_ifs <;> push_neg
      · case pos _ => intro h; contradiction
      · case pos _ => intro h; contradiction
      · case pos h1 h2 _ => intro _; exact Decidable.not_imp_iff_and_not.mp fun a ↦ h2 (a h1)
      · case neg h1 h2 _ => intro _; exact Decidable.not_imp_iff_and_not.mp fun a ↦ h2 (a h1)
   · case mpr =>
      push_neg
      intro ⟨h1,h2⟩
      split_ifs <;> try contradiction
      · case pos _ h3 =>
          rw [square_roots_elem_iff_square_root S x]
          exact h3.symm
      . case neg _ _ _ => exact arbitraryRoot_root S hsurj x

theorem square_root_or_square (x y : M) :
 Magma.op (self:= instMagma S hsurj) x y ∈ square_roots S x ∨
 Magma.op (self:= instMagma S hsurj) x y = S x := by
   by_cases h : (S x = S y ∨ x = S y)
   · case pos => right; exact (square_iff_eq S hsurj hnofix x y).mpr h
   · case neg => left; exact (square_root_iff_neq S hsurj hnofix x y).mpr h

-- Also we have `x ⋄ x = S x`, justifying the interpretation of `S` as a squaring map.
omit hnofix in
theorem squaring_map (x : M) : Magma.op (self:= instMagma S hsurj) x x = S x := by
   simp [Magma.op, magmaOp]

omit hnofix in
lemma square_times_square_root_eq_elem' (x : M) :
  Magma.op (self:= instMagma S hsurj) (S (S x)) x = S x := by
   simp [Magma.op, magmaOp]
   split_ifs <;> aesop

-- By construction, `S x ⋄ √x = x`
omit hnofix in
theorem square_times_square_root_eq_elem {x y : M} (hsq : y ∈ square_roots S x):
  Magma.op (self:= instMagma S hsurj) (S x) y = x := by
    have hsy : S y = x := by exact hsq
    rw [← hsy]
    exact square_times_square_root_eq_elem' S hsurj y

-- and `√x ⋄ √x = x`
omit hnofix in
theorem square_root_times_square_root_eq_elem {x y z : M} (hsqy : y ∈ square_roots S x) (hsqz : z ∈ square_roots S x):
  Magma.op (self:= instMagma S hsurj) y z = x := by
    have hsy : S y = x := by exact hsqy
    have hsz : S z = x := by exact hsqz
    simp only [Magma.op, magmaOp]
    split_ifs <;> try aesop
    · case pos h1 h2 => rw [hsy, hsz] at h1; contradiction
    · case pos h1 h2 h3 => exact hsz

omit hnofix in
lemma S_times_eq_S_squared (x : M) :
  Magma.op (self := instMagma S hsurj) (S x) x = S (S x) := by
   simp [Magma.op, magmaOp]

--lemma times_S_squared_eq_S_cubed (x : M) :
--  Magma.op (self := instMagma S hsurj) x (S (S x)) = S (S (S x)) := by
--   simp [Magma.op, magmaOp]

/-
By construction, we just need to rule out the possibility that `S (z ⋄ x) = S x` or `S (z ⋄ x) = x`. There are four cases:

    If `S (z ⋄ x) = S x` and `z ⋄ x` was a square root of `z` then `z = S x`, but then `S (z ⋄ x) = S^3 x ≠ S x`, contradiction.
    If `S (z ⋄ x) = S x` and `z ⋄ x = S z` then `S z = S x` or `z = S x`, so `S x = S^2 x` or `S x = S^3 x`, contradiction.
    If `S (z ⋄ x) = x` and `z ⋄ x` was a square root of `z` then `z = x`, but then `S (z ⋄ x) = S^2 x ≠ x`, contradiction.
    If `S (z ⋄ x) = x` and `z ⋄ x = S z` then `S z = S x` or `z = S x`, but then `x = S^2 x` or `x = S^3 x`, contradiction.

-/
theorem elem_mul_other_mul_elem_square_root (x z : M) :
  Magma.op (self:= instMagma S hsurj) x (Magma.op (self:= instMagma S hsurj) z x) ∈ square_roots S x := by
    have hsq' := square_root_or_square S hsurj hnofix x (Magma.op z x (self:=instMagma S hsurj))
    cases hsq'
    · case inl h => exact h
    · case inr h =>
        have h1 := (square_iff_eq S hsurj hnofix x  _).1 h
        have h2 := square_root_or_square S hsurj hnofix z x
        cases h1 <;> cases h2 <;> exfalso
        · case inl.inl h1 h2 =>
            rw [square_roots_elem_iff_square_root, ← h1] at h2
            rw [← h2, S_times_eq_S_squared ] at h
            rw [← h2, S_times_eq_S_squared ] at h1
            apply (hnofix (S x)).2.1
            exact h1.symm
        . case inl.inr h1 h2 =>
            have h3 := square_iff_eq S hsurj hnofix z x |>.1 h2
            cases h3
            · case inl h3 =>
                rw [h3] at h2
                rw [h2] at h1
                apply (hnofix (S x)).1
                exact h1.symm
            · case inr h3 =>
                nth_rw 2 [h3] at h2
                rw [h2] at h1
                apply (hnofix (S x)).2.1
                exact h1.symm
        · case inr.inl h1 h2 =>
            rw [square_roots_elem_iff_square_root, ← h1] at h2
            rw [← h2, squaring_map] at h1
            apply (hnofix x).2.1
            exact h1.symm
        · case inr.inr h1 h2 =>
            have h3 := square_iff_eq S hsurj hnofix z x |>.1 h2
            cases h3
            · case inl h3 =>
                rw [h2, h3] at h1
                apply (hnofix x).2.1
                exact h1.symm
            · case inr h3 =>
                rw [h2, h3] at h1
                apply (hnofix x).2.2
                exact h1.symm

-- so it suffices to show that `x ⋄ (z ⋄ x) ∈ √x`
theorem M_satisfies_Equation1447 : @Equation1447 M (instMagma S hsurj) := by
  intro x y z
  have hsq := square_root_or_square S hsurj hnofix x y
  have hsqrt := elem_mul_other_mul_elem_square_root S hsurj hnofix x z
  symm
  cases hsq
  · case inl h =>
     apply square_root_times_square_root_eq_elem S hsurj h hsqrt
  · case inr h =>
      rw [h]
      apply square_times_square_root_eq_elem S hsurj hsqrt

end Construction

section ConcreteRefutations

noncomputable abbrev iota : ℝ → UnitAddCircle := fun x => ↑x

def M := Set.image iota {x : ℝ | Irrational x}

def S : M → M := fun ⟨x,h⟩ =>
  ⟨x*2, Irrational.mul_rat h (by decide)⟩
theorem S.surjective : Function.Surjective S := by
  simp [Function.Surjective, M]
  intro a ha
  have ha12  := Irrational.mul_rat ha (q := 1/2) (by simp)
  have h12 : @Rat.cast ℝ Real.instRatCast (1 / 2)  = @HDiv.hDiv ℝ ℝ ℝ instHDiv 1 2  := by simp
  have hprod : S ⟨a * ↑(1 / 2), h12 ▸ ha12⟩ = ⟨a,ha⟩ := by
    simp [S]
  exists a * ↑(1 / 2)
  exists h12 ▸ ha12

theorem S.nofix : no_fixed_points S := by
  simp [no_fixed_points, S]
  intro a ha
  push_neg
  constructor <;> try constructor
  · sorry
  · sorry
  · sorry

theorem M_1_satisfies_Equation1447 : @Equation1447 M (instMagma S S.surjective) :=
  M_satisfies_Equation1447 S S.surjective S.nofix

#check M_satisfies_Equation1447
#print Equation1431
#print Equation4269

end ConcreteRefutations
#synth Coe Real UnitAddCircle

end Equation1447
