import Mathlib.Data.Countable.Defs
import Mathlib.Data.Sum.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
  In this file we construct (using choice) for a given countable type `α` and an natural number `m`
  an equivalence `adjoinFresh m : ℕ ≃ ℕ ⊕ α` that agrees with the inclusion `Sum.inl` on the numbers
  smaller than `m`.
-/

namespace AdjoinFresh
universe u

variable {α : Type u} [Countable α]

private noncomputable def e : ℕ ≃ ℕ ⊕ α := Classical.choice (inferInstance : Nonempty (ℕ ≃ ℕ ⊕ α))

noncomputable def adjoinFresh (m : ℕ) : ℕ ≃ ℕ ⊕ α where
  toFun n := if n < m then .inl n else match e (n - m) with
    | .inl k => .inl (k + m)
    | .inr c => .inr c
  invFun
    | .inl k => if k < m then k else e.symm (.inl (k-m)) + m
    | .inr c => e.symm (.inr c) + m
  left_inv n := by
    dsimp
    by_cases h : n < m
    · simp [h]
    · simp [h]
      cases h' : (e (α:=α) (n -m))
      · simp only [add_lt_iff_neg_right, not_lt_zero', ↓reduceIte, add_tsub_cancel_right]
        rw [← h']
        simp only [Equiv.symm_apply_apply]
        aesop
      · simp [← h']
        omega
  right_inv a := by
    cases a
    case inl n =>
      simp only
      by_cases h : n < m
      · simp [h]
      · simp only [h, ↓reduceIte, Nat.add_sub_cancel, Equiv.apply_symm_apply]
        have : ¬ ((e (α := α)).symm (Sum.inl (n - m)) + m < m) := by omega
        simp only [this, ↓reduceIte, Sum.inl.injEq]
        omega
    case inr => simp

theorem adjoinFresh_fixed {m k: ℕ} (h : k  < m) :
  adjoinFresh (α := α) m k = .inl k := by unfold adjoinFresh; simp [h]

theorem adjoinFresh_fixed' {m k: ℕ} (h : k  < m) :
  (adjoinFresh (α := α ) m).symm (.inl k) = k := by unfold adjoinFresh; simp [h]
