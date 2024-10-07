import Mathlib.Tactic
import equational_theories.AllEquations
import equational_theories.EquationalResult

/-!
This file is a home for manual proofs of refutations that require constructions
of infinite models.
-/

namespace InfiniteModels

lemma xor_even_even {a b : ℕ} (ha : Even a) (hb : Even b) : Even (a ^^^ b) := by
  by_contra! H
  rw [Nat.not_even_iff_odd, Nat.odd_iff] at H
  rw [Nat.xor_mod_two_eq_one] at H
  rw [←Nat.odd_iff, ←Nat.not_even_iff_odd] at H
  rw [←Nat.odd_iff, ←Nat.not_even_iff_odd] at H
  aesop

lemma xor_even_add_two {a : ℕ} (ha : Even a) : Even (a + 2) := by
  obtain ⟨t, rfl⟩ := ha
  use t + 1
  ring

lemma xor_even_sub_two {a : ℕ} (ha : Even a) : Even (a - 2) := by
  obtain ⟨t, rfl⟩ := ha
  cases' t with t
  · simp
  · use t; omega

def f_3994_3588 (x y : ℕ) : ℕ :=
  if Even x then
    if Even y then
      x ^^^ y
    else
      x - 2
  else
    if Even y then
     y + 2
    else 0

@[equational_result]
theorem Equation3994_not_implies_Equation3588 :
    ∃ (G: Type) (_: Magma G), Equation3994 G ∧ ¬ Equation3588 G := by
  refine ⟨ℕ, { op := f_3994_3588 }, ?_, ?_⟩
  · intro x y z
    simp only [Magma.op, f_3994_3588]
    by_cases hx : Even x
    · simp only [hx, reduceIte]
      by_cases hy : Even y
      · have hxy := xor_even_even hx hy
        simp only [hy, reduceIte]
        by_cases hz : Even z
        · simp only [hz, reduceIte, hxy, xor_even_even hz hxy]
          rw [←Nat.xor_comm z]
          exact (Nat.xor_cancel_left z (x ^^^ y)).symm
        · simp [hz, hxy, xor_even_add_two]
      · simp only [hy, reduceIte]
        have hx' := xor_even_sub_two hx
        by_cases hz : Even z
        · simp only [hz, reduceIte, hx', xor_even_sub_two, xor_even_even]
          rw [Nat.xor_comm]
          exact (Nat.xor_cancel_left z (x - 2)).symm
        · simp [hz, hx', xor_even_add_two hx']
    · simp [hx]
      by_cases hy : Even y
      · simp only [hy, reduceIte]
        have hy' := xor_even_add_two hy
        by_cases hz : Even z
        · simp only [hz, reduceIte, hy', xor_even_even hz hy']
          rw [Nat.xor_comm]
          exact (Nat.xor_cancel_left z (y + 2)).symm
        · simp [hz, hy', xor_even_add_two hy']
      · simp only [hy, reduceIte]
        by_cases hz : Even z <;> simp [hz]
  · intro h
    specialize h 1 1 1
    simp [Magma.op, f_3994_3588] at h

-- TODO dual of the above (eq3588 and eq3994 are dual with each other).
