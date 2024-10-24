/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import equational_theories.FreeMagma
import equational_theories.MagmaLaw
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Logic.Equiv.TransferInstance

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
    intro h a
    cases' a with a l r
    · intro h; simp at h
    · refine fun h1 h2 ↦ h ?_
      trans (order l, order r)
      · simp at h1; simp [h1]
      · simp at h2; simp [h2]

end FreeMagma

namespace FreeMagma

instance : MulAction (Equiv.Perm X) (FreeMagma X) where
  smul π w := fmapHom π w
  one_smul := fmapHom_id
  mul_smul :=
    fun π1 π2 w => by symm; apply fmapHom_comp'

end FreeMagma

namespace Law

@[simp]
def order : MagmaLaw X → ℕ :=
  fun E => FreeMagma.order E.lhs + FreeMagma.order E.rhs

instance : MulAction (Equiv.Perm X) (MagmaLaw X) := by
  refine' Equiv.mulAction (Equiv.Perm X) (_: _ ≃ FreeMagma X × FreeMagma X)
  constructor
    <;> try exact fun ⟨lhs, rhs⟩ => ⟨lhs, rhs⟩
  all_goals intro; rfl

namespace UpToRelabelling

def rel : Setoid (MagmaLaw X) :=
  MulAction.orbitRel (Equiv.Perm X) (MagmaLaw X)
def MagmaLaw (α: Type*) := Quotient (rel: Setoid (Law.MagmaLaw α))

def order : MagmaLaw X → ℕ := by
  refine' Quotient.lift Law.order _
  rintro ⟨w1, w2⟩ ⟨w1', w2'⟩ ⟨π, smul_π_E'_eq_E⟩
  simp_all [HSMul.hSMul, SMul.smul]
  rcases smul_π_E'_eq_E with ⟨smul_π_w1_eq_w1', smul_π_w2_eq_w2'⟩
  revert w1 w2 w1' w2'
  suffices ∀ w w', w' = FreeMagma.fmapHom π w → w'.order = w.order by
    intros
    congr 1
    all_goals {
      apply this
      simp_all [this]
    }
  intros w w' smul_π_w_eq_w'
  subst smul_π_w_eq_w'
  induction w
  .
    simp_all [FreeMagma.order]
  .
    rename_i w1 w2 order_smul_π_w1_eq_order_w1 order_smul_π_w2_eq_order_w2
    simp_all [FreeMagma.fmapHom, FreeMagma.order]

def bell : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Fin n.succ, (n.choose k) * bell k

theorem card_subtype_laws_of_order_eq (n: ℕ) :
  Cardinal.mk { x : MagmaLaw ℕ // order x = n } = ↑(catalan (n+1) * bell (n+2): ℕ) := by
  sorry

end UpToRelabelling

end Law
