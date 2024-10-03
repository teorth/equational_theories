import Mathlib.Algebra.Group.Nat

@[simp]
theorem Nat.xor_mod_two_eq (a b : ℕ) : (a ^^^ b) % 2 = (a + b) % 2 := by
  by_cases h : (a + b) % 2 = 0
  · simp only [h, mod_two_eq_zero_iff_testBit_zero, testBit_zero, xor_mod_two_eq_one, decide_not,
    Bool.decide_iff_dist, Bool.not_eq_false', beq_iff_eq, decide_eq_decide]
    omega
  · simp only [mod_two_ne_zero] at h
    simp [h]
    omega

@[simp]
theorem Nat.even_xor (a b : ℕ) : Even (a ^^^ b) ↔ (Even a ↔ Even b) := by
  simp only [even_iff, xor_mod_two_eq]
  simp [← even_iff]
  exact even_add
