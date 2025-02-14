-- This file mechanizes the construction described in:
-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/713.2C.201289.2C.201447/near/482236139
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Topology.Instances.AddCircle
import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.FactsSyntax

namespace Equation1447

section Construction
universe u

-- Select a surjective map `S : M → M` as the candidate squaring map
variable {M : Type u} (S : M → M)

-- with the property that S, S^2, S^3 have no fixed points
def no_fixed_points : Prop := ∀ (m : M), S m ≠ m ∧ S (S m) ≠ m ∧ S (S (S m)) ≠ m

variable (hnofix : no_fixed_points S)
include hnofix

def square_roots (x : M) : Set M := { y : M | S y = x }

notation "√" => square_roots

omit hnofix in
lemma square_roots_elem_iff_square_root (x y : M) :
  y ∈ square_roots S x ↔ S y = x := Set.mem_def

-- which is disjoint from both `x` and `S x`.
theorem elem_notin_square (x : M) : x ∉ square_roots S x := by
  exact (hnofix x).1

theorem s_elem_notin_square (x : M) : S x ∉ square_roots S x := by
  exact (hnofix x).2.1

-- One can think of `S x` as the "parent" of `x`, and the elements of √`x`
-- ​ as "siblings" to each other, and "children" of `x`.
def parent (x : M) (y : M) : Prop := y = S x
def sibling (x : M) (y : M) : Prop := ∃ (z : M), x ∈ square_roots S z ∧ y ∈ square_roots S z
def child (x : M) (y : M) : Prop := x ∈ square_roots S y

variable  [DecidableEq M]

variable (arbitraryRoot : M → M)

variable (arbitraryRoot_root : ∀ (x : M), arbitraryRoot x ∈ square_roots S x)
include arbitraryRoot_root

-- Define `x⋄y` to equal `S x` if `S x = S y` or `x = S y`; equal to `S y` if `x = S^2 y`; and equal to an arbitrary square root in `x`
-- ​ otherwise.
noncomputable def magmaOp : M → M → M := fun x y =>
  if S x = S y then S x else
  if x = S y then S x else
  if x = S (S y) then S y
  else arbitraryRoot x

noncomputable instance instMagma : Magma M where
  op := magmaOp S arbitraryRoot

-- Observe that `x ⋄ y` is either the square of `x` or a square root of `x`,
-- with the former possibility occurring if and only if `S x = S y` or `x = S y`
-- (i.e. `x` is a parent or sibling of `y`).
theorem square_iff_eq (x y : M) :
 Magma.op (self:= instMagma S arbitraryRoot) x y = S x
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
          exact arbitraryRoot_root x
   · case mpr =>
      intro h
      cases h <;> split_ifs <;> aesop

theorem square_root_iff_neq (x y : M) :
 Magma.op (self:= instMagma S arbitraryRoot) x y ∈ square_roots S x
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
      . case neg _ _ _ => exact arbitraryRoot_root x

theorem square_root_or_square (x y : M) :
 Magma.op (self:= instMagma S arbitraryRoot) x y ∈ square_roots S x ∨
 Magma.op (self:= instMagma S arbitraryRoot) x y = S x := by
   by_cases h : (S x = S y ∨ x = S y)
   · case pos => right; exact (square_iff_eq S hnofix arbitraryRoot arbitraryRoot_root x y).mpr h
   · case neg => left; exact (square_root_iff_neq S hnofix arbitraryRoot arbitraryRoot_root x y).mpr h

-- Also we have `x ⋄ x = S x`, justifying the interpretation of `S` as a squaring map.
omit hnofix arbitraryRoot_root in
theorem squaring_map (x : M) : Magma.op (self:= instMagma S arbitraryRoot) x x = S x := by
   simp [Magma.op, magmaOp]

omit hnofix arbitraryRoot_root in
lemma square_times_square_root_eq_elem' (x : M) :
  Magma.op (self:= instMagma S arbitraryRoot) (S (S x)) x = S x := by
   simp [Magma.op, magmaOp]
   split_ifs <;> aesop

-- By construction, `S x ⋄ √x = x`
omit hnofix arbitraryRoot_root in
theorem square_times_square_root_eq_elem {x y : M} (hsq : y ∈ square_roots S x):
  Magma.op (self:= instMagma S arbitraryRoot) (S x) y = x := by
    have hsy : S y = x := hsq
    rw [← hsy]
    exact square_times_square_root_eq_elem' S arbitraryRoot y

-- and `√x ⋄ √x = x`
omit hnofix arbitraryRoot_root in
theorem square_root_times_square_root_eq_elem {x y z : M} (hsqy : y ∈ square_roots S x) (hsqz : z ∈ square_roots S x):
  Magma.op (self:= instMagma S arbitraryRoot) y z = x := by
    have hsy : S y = x := hsqy
    have hsz : S z = x := hsqz
    simp only [Magma.op, magmaOp]
    split_ifs <;> try aesop
    -- · case pos  => exact hsqy
    -- · case pos => exact hsqz

omit hnofix arbitraryRoot_root in
lemma S_times_eq_S_squared (x : M) :
  Magma.op (self := instMagma S arbitraryRoot) (S x) x = S (S x) := by
   simp [Magma.op, magmaOp]

/-
By construction, we just need to rule out the possibility that `S (z ⋄ x) = S x` or `S (z ⋄ x) = x`. There are four cases:

    If `S (z ⋄ x) = S x` and `z ⋄ x` was a square root of `z` then `z = S x`, but then `S (z ⋄ x) = S^3 x ≠ S x`, contradiction.
    If `S (z ⋄ x) = S x` and `z ⋄ x = S z` then `S z = S x` or `z = S x`, so `S x = S^2 x` or `S x = S^3 x`, contradiction.
    If `S (z ⋄ x) = x` and `z ⋄ x` was a square root of `z` then `z = x`, but then `S (z ⋄ x) = S^2 x ≠ x`, contradiction.
    If `S (z ⋄ x) = x` and `z ⋄ x = S z` then `S z = S x` or `z = S x`, but then `x = S^2 x` or `x = S^3 x`, contradiction.

-/
theorem elem_mul_other_mul_elem_square_root (x z : M) :
  Magma.op (self:= instMagma S arbitraryRoot) x (Magma.op (self:= instMagma S arbitraryRoot) z x) ∈ square_roots S x := by
    have hsq' := square_root_or_square S hnofix arbitraryRoot arbitraryRoot_root x (Magma.op z x (self:=instMagma S arbitraryRoot))
    cases hsq'
    · case inl h => exact h
    · case inr h =>
        have h1 := (square_iff_eq S hnofix arbitraryRoot arbitraryRoot_root x  _).1 h
        have h2 := square_root_or_square S hnofix arbitraryRoot arbitraryRoot_root z x
        cases h1 <;> cases h2 <;> exfalso
        · case inl.inl h1 h2 =>
            rw [square_roots_elem_iff_square_root, ← h1] at h2
            rw [← h2, S_times_eq_S_squared ] at h
            rw [← h2, S_times_eq_S_squared ] at h1
            apply (hnofix (S x)).2.1
            exact h1.symm
        . case inl.inr h1 h2 =>
            have h3 := square_iff_eq S hnofix arbitraryRoot arbitraryRoot_root z x |>.1 h2
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
            have h3 := square_iff_eq S hnofix arbitraryRoot arbitraryRoot_root z x |>.1 h2
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
theorem M_satisfies_Equation1447 : @Equation1447 M (instMagma S arbitraryRoot) := by
  intro x y z
  have hsq := square_root_or_square S hnofix arbitraryRoot arbitraryRoot_root x y
  have hsqrt := elem_mul_other_mul_elem_square_root S hnofix  arbitraryRoot arbitraryRoot_root x z
  symm
  cases hsq
  · case inl h =>
     apply square_root_times_square_root_eq_elem S arbitraryRoot h hsqrt
  · case inr h =>
      rw [h]
      apply square_times_square_root_eq_elem S arbitraryRoot hsqrt

end Construction

section ConcreteRefutations

-- This feels unnecessarily tedious
lemma S.well_def (n : PNat) (hn : n.val ≠ 1) : 0 < n.val / (2 : Nat) := by
  obtain ⟨n',hn'⟩ := n
  have hn : n' > 1 := by
    simp at hn
    omega
  simp
  omega

def S : PNat → PNat := fun n =>
  if h : n.val = 1 then 8 else ⟨n.val / (2 : Nat), S.well_def n h⟩

theorem pval_eq_val_eq (m n : PNat) : m = n ↔ m.val = n.val := by simp

lemma n_gt_1_s_eq_div_2 (n : PNat) (hn : n.val > 1) : S n = n.val / 2 := by
  simp [S]
  aesop

lemma n_gt_3_s_s_eq_div_4 (n : PNat) (hn : n.val > 3) : S (S n) = n.val / 4 := by
  have hn2 := n_gt_1_s_eq_div_2 n (by omega)
  have hn2' : S n = ⟨(n / 2), by omega⟩ := by
    apply (pval_eq_val_eq _ _).2
    exact hn2
  have hn2gt1 : n.val / 2 > 1 := by omega
  rw [hn2']
  rw [n_gt_1_s_eq_div_2 ⟨(n / 2), by omega⟩ hn2gt1]
  simp
  omega

lemma n_gt_7_s_s_s_eq_div_8 (n : PNat) (hn : n.val > 7) : S (S (S n)) = n.val / 8 := by
  have hn2 := n_gt_1_s_eq_div_2 n (by omega)
  have hn2' : S n = ⟨(n / 2), by omega⟩ := by
    apply (pval_eq_val_eq _ _).2
    exact hn2
  have hn2gt1 : n.val / 2 > 3 := by omega
  rw [hn2']
  rw [n_gt_3_s_s_eq_div_4 ⟨(n / 2), by omega⟩ hn2gt1]
  simp
  omega

-- TODO: golf this, there should be a nicer way...
lemma S.nofix_le_7 (n : PNat) (hn : n.val ≤ 7) : S n ≠ n ∧ S (S n) ≠ n ∧ S (S (S n)) ≠ n := by
  have hnzero : n.val > 0 := n.prop
  have casesplit : n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨ n.val = 4 ∨ n.val = 5 ∨ n.val = 6 ∨ n.val = 7 := by omega
  simp [Ne]
  repeat rw [pval_eq_val_eq ]
  cases casesplit
  · case inl h => simp [S,h]
  · case inr caseplit =>
      cases caseplit
      · case inl h => simp [S,h]
      · case inr caseplit =>
          cases caseplit
          · case inl h => simp [S,h]
          · case inr caseplit =>
              cases caseplit
              · case inl h => simp [S,h]
              · case inr caseplit =>
                  cases caseplit
                  · case inl h => simp [S,h]
                  · case inr caseplit =>
                      cases caseplit
                      · case inl h => simp [S,h]
                      · case inr h => simp [S,h]

lemma S.nofix_gt_7 (n : PNat) (hn : n.val > 7) : S n ≠ n ∧ S (S n) ≠ n ∧ S (S (S n)) ≠ n := by
  have hgt1 : n.val > 1 := by omega
  have hgt3 : n.val > 3 := by omega
  have hs := n_gt_1_s_eq_div_2 n hgt1
  have hs_s := n_gt_3_s_s_eq_div_4  n hgt3
  have hs_s_s := n_gt_7_s_s_s_eq_div_8 n hn
  simp_all [pval_eq_val_eq]
  omega

theorem S.nofix : no_fixed_points S := by
  intro ⟨n,hn⟩
  by_cases n > 7
  · case pos h =>
      apply S.nofix_gt_7 ⟨n,hn⟩ h
  · case neg h =>
      have hleq : n ≤ 7 := by omega
      apply S.nofix_le_7 ⟨n,hn⟩ hleq

def arbitraryRoot : PNat → PNat := fun n =>
  n * 2

theorem arbitraryRoot_root : ∀ (x : PNat), arbitraryRoot x ∈ square_roots S x := by
  simp [arbitraryRoot, square_roots, S]
  intro ⟨n, hn⟩
  split_ifs
  · case pos h => exfalso; simp [pval_eq_val_eq] at h
  · simp [pval_eq_val_eq]

theorem PNat_S_satisfies_Equation1447 : @Equation1447 PNat (instMagma S arbitraryRoot) :=
  M_satisfies_Equation1447 S S.nofix arbitraryRoot arbitraryRoot_root

theorem PNat_S_refutes_Equation1431 : ¬ @Equation1431 PNat (instMagma S arbitraryRoot) := by
  simp [Equation1431]
  exists 1
  exists 3

theorem PNat_S_refutes_Equation4269 : ¬ @Equation4269 PNat (instMagma S arbitraryRoot) := by
  simp [Equation1431]
  exists 1
  exists 3

@[equational_result]
theorem Equation1447_facts :
  ∃ (G : Type) (_ : Magma G), Facts G [1447] [1431, 4269]:= by
  exists PNat
  exists instMagma S arbitraryRoot
  constructor
  · exact PNat_S_satisfies_Equation1447
  · constructor
    exact PNat_S_refutes_Equation1431
    exact PNat_S_refutes_Equation4269

end ConcreteRefutations
end Equation1447
