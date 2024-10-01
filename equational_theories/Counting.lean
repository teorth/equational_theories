/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import equational_theories.FreeMagma
import Mathlib.Combinatorics.Enumerative.Catalan

variable {X : Type*}

namespace FreeMagma

def order : FreeMagma X → ℕ
  | Lf _ => 0
  | a ⋆ b => order a + order b + 1

@[simp]
lemma order_leaf (a : X) : (Lf a).order = 0 := rfl

@[simp]
lemma order_fork (a b : FreeMagma X) : (a ⋆ b).order = a.order + b.order + 1 := rfl

-- Compare to `Tree.pairwiseNode`
abbrev pairwiseFork (a b : Finset (FreeMagma X)) : Finset (FreeMagma X) :=
  (a ×ˢ b).map ⟨fun ⟨x, y⟩ ↦ x ⋆ y, fun ⟨a, b⟩ ⟨c, d⟩ ↦ by simp⟩

variable (X) [Fintype X] [DecidableEq X]

-- Compare to `Tree.treesOfNumNodesEq`
def elementsOfNumNodesEq : ℕ → Finset (FreeMagma X)
  | 0 => Finset.univ.map ⟨Lf, fun a b h ↦ by simpa using h⟩
  | n + 1 =>
    (Finset.antidiagonal n).attach.biUnion fun ijh =>
      pairwiseFork (elementsOfNumNodesEq ijh.1.1) (elementsOfNumNodesEq ijh.1.2)
  -- Porting note: Add this to satisfy the linter.
  decreasing_by
    · simp_wf; have := Finset.antidiagonal.fst_le ijh.2; omega
    · simp_wf; have := Finset.antidiagonal.snd_le ijh.2; omega

-- Compare to `Tree.treesOfNumNodesEq_zero`
@[simp]
theorem elementsOfNumNodesEq_zero : elementsOfNumNodesEq X 0 =
    Finset.univ.map ⟨Lf, fun a b h ↦ by simpa using h⟩ := by rw [elementsOfNumNodesEq]

-- Compare to `Tree.treesOfNumNodesEq_succ`
theorem elementsOfNumNodesEq_succ {n : ℕ} : elementsOfNumNodesEq X (n + 1) =
    (Finset.antidiagonal n).biUnion fun ijh => pairwiseFork (elementsOfNumNodesEq X ijh.1)
      (elementsOfNumNodesEq X ijh.2) := by
  rw [elementsOfNumNodesEq]
  ext
  simp

-- Compare to `Tree.mem_treesOfNumNodesEq`
@[simp]
theorem mem_elementsOfNumNodesEq {x : FreeMagma X} {n : ℕ} :
    x ∈ elementsOfNumNodesEq X n ↔ order x = n := by
  induction x generalizing n <;> cases n
  · simp
  · simp [elementsOfNumNodesEq_succ]
  · simp
  · simp [elementsOfNumNodesEq_succ, *]

-- Compare to `Tree.treesOfNumNodesEq_card_eq_catalan`
theorem elementsOfNumNodesEq_card_eq_catalan_mul_pow (n : ℕ) :
    (elementsOfNumNodesEq X n).card = catalan n * (Fintype.card X) ^ (n + 1) := by
  induction' n using Nat.case_strong_induction_on with n ih
  · simp
  rw [elementsOfNumNodesEq_succ, Finset.card_biUnion, catalan_succ', Finset.sum_mul]
  · apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ h
    rw [Finset.card_map, Finset.card_product, ih _ (Finset.antidiagonal.fst_le h),
      ih _ (Finset.antidiagonal.snd_le h)]
    rw [← Finset.mem_antidiagonal.1 h]
    ring
  · simp_rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ _ ⟨i', j'⟩ _
    intros h a
    cases' a with a l r
    · intro h; simp at h
    · intro h1 h2
      apply h
      trans (order l, order r)
      · simp at h1; simp [h1]
      · simp at h2; simp [h2]


end FreeMagma
