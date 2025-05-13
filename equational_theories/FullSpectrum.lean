import equational_theories.Equations.All
import Init.Data.Int.DivMod.Lemmas
import equational_theories.MagmaOp
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic.Zify

/-! Equations with finite models of every cardinality are denoted 'full spectrum', see
https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Equations.20with.20full.20spectrum

This file proves that 7 equations are full spectrum and 32 are not: this should be a complete result
for all order 4 equations through transitivity and duality. (All equations that are implied by a
full spectrum equation must be full spectrum and all equations that imply a not-full-spectrum
equation, must not be full spectrum.)

Some automatically generated proofs are in `Generated/FullSpectrum.lean`, for equations that are not
full spectrum that have models of size 2 but not 3.

TODO: Prove that the 7+32 equations above are actually complete.
-/

namespace FullSpectrum

abbrev EqFullSpectrum (Eq : (G: Type) -> (_: Magma G) -> Prop) :=
  ∀ n : ℕ, ∃ (M : Magma (Fin n)), Eq (Fin n) M

syntax "HasFullSpectrum [" num,* "]" : term
open Lean Meta Elab Term Tactic Parser.Term in
elab_rules : term | `(HasFullSpectrum [ $eqs,* ]) => do
  let s := eqs.getElems.map fun ⟨s⟩ =>
    mkApp (mkConst ``EqFullSpectrum) (mkConst (.mkSimple s!"Equation{s.toNat}") [0])
  let e := mkAndN s.toList
  return e

syntax "NotFullSpectrum [" num,* "]" : term
open Lean Meta Elab Term Tactic Parser.Term in
elab_rules : term | `(NotFullSpectrum [ $eqs,* ]) => do
  let s := eqs.getElems.map fun ⟨s⟩ =>
    mkApp (mkConst ``Not)
      (mkApp (mkConst ``EqFullSpectrum) (mkConst (.mkSimple s!"Equation{s.toNat}") [0]))
  let e := mkAndN s.toList
  return e

example : HasFullSpectrum [1] := by
  intro n
  use ⟨fun x y => x⟩
  simp [Equation1]

example : NotFullSpectrum [2] := by
  simp only [not_exists, not_forall]
  use 2
  exact fun m => ⟨0, 1, by simp⟩

theorem full_spectrum_left_absorptive : HasFullSpectrum [4] := by
  intro n
  use ⟨fun x y => x⟩
  simp [Equation4]

theorem full_spectrum_constant : HasFullSpectrum [41] := by
  intro n
  if h : 0 < n then
    let op (x y : Fin n) : Fin n := ⟨0, h⟩
    use ⟨op⟩
    simp [Equation41]
  else
    use ⟨fun x y => x⟩
    omega

theorem full_spectrum_square_cancellative : HasFullSpectrum [1523] := by
  intro n
  if h : n > 0 then
    let op (x y : Fin n) : Fin n := ⟨
      if x.1 = y.1 then 0
      else if x.1 = 0 then y
      else x,
      by
        repeat' split
        all_goals simp [h]
    ⟩
    use ⟨op⟩
    intro x _
    rcases eq_or_ne x.1 0 with h | h
    . simp [op, h, Fin.eq_mk_iff_val_eq]
    . simp [op, h, h.symm, Fin.eq_mk_iff_val_eq]
  else
    use ⟨fun x y => x⟩
    omega

@[simp] private theorem emod_sub_emod (m n k : Int) : (m % n - k) % n = (m - k) % n :=
  Int.emod_add_emod m n (-k)

@[simp] private theorem sub_emod_emod (m n k : Int) : (m - n % k) % k = (m - n) % k := by
  apply (Int.emod_add_cancel_right (n % k)).mp
  rw [Int.sub_add_cancel, Int.add_emod_emod, Int.sub_add_cancel]

private lemma linear₁ {a n : Int} (h : n ≠ 0) : a % n ⊔ 0 = a % n := by
  have : 0 ≤ a % n := (Int.emod_nonneg a) h
  exact Int.max_eq_left this
private lemma linear₂ {a n : Nat} (h : a < n) : ((a : Int) % (n : Int)).toNat = a := by
  simp [Int.toNat, Int.ofNat_mod_ofNat, Nat.mod_eq_of_lt h]

theorem full_spectrum_linear_cancellative1 : HasFullSpectrum [492] := by
  intro n
  if h : n > 0 then
    let op (x y : Fin n) : Fin n := ⟨((n : ℤ) - ↑x + ↑n - ↑y).natMod ↑n, Int.natMod_lt (ne_of_gt h)⟩
    use ⟨op⟩
    intro _ _ _
    apply Fin.eq_mk_iff_val_eq.mpr
    zify at h
    simp only [Int.natMod, Int.ofNat_toNat, linear₁ (ne_of_gt h), sub_emod_emod]
    simp [Int.add_sub_assoc, ←Int.sub_sub, linear₂]
  else
    use ⟨fun x y => x⟩
    omega

theorem full_spectrum_linear_cancellative2 : HasFullSpectrum [1090] := by
  intro n
  if h : n > 0 then
    let op (x y : Fin n) : Fin n := ⟨((n : ℤ) - ↑x + ↑y).natMod ↑n, Int.natMod_lt (ne_of_gt h)⟩
    use ⟨op⟩
    intro _ _ _
    apply Fin.eq_mk_iff_val_eq.mpr
    have (m n o k : Int) : (k - m % n + o) % n = (k - m + o) % n := by
      apply (Int.emod_add_cancel_right (-o)).mp
      simp
    zify at h
    simp only [Int.natMod, Int.ofNat_toNat, linear₁ (ne_of_gt h), Int.add_emod_emod, this]
    simp [Int.add_sub_assoc, ←Int.sub_sub, linear₂]
  else
    use ⟨fun x y => x⟩
    omega

theorem full_spectrum_Equation1482 : HasFullSpectrum [1482] := by
  intro n
  if h : n > 1 then
    let op (x y : Fin n) : Fin n := ⟨
      if y.1 = 1 then
        if x.1 > 1 then x.1
        else if x.1 = 1 then 0
        else 1
      else if x.1 = 1 && y.1 > 1 then y.1
      else 1,
      by
        repeat' split
        all_goals simp only [x.2, y.2, h, Nat.zero_lt_of_lt h]⟩
    use ⟨op⟩
    intro x _
    apply Fin.eq_mk_iff_val_eq.mpr
    simp only [Bool.and_self, decide_eq_true_eq, gt_iff_lt, Bool.and_eq_true]
    split
    . simp only [lt_self_iff_false, ↓reduceIte, zero_ne_one, not_lt_zero', and_false, true_and, *]
      split
      . simp [*]
      . split
        . rfl
        . simp [show x.1 = 0 by omega]
    . simp only [false_and, ↓reduceIte, ite_eq_right_iff, imp_false, not_lt, *]
      split
      . simp [show ¬x.1 = 1 by omega, *]
      . split
        . simp [*]
        . simp [show x.1 = 0 by omega]
  else
    use ⟨fun x y => x⟩
    omega

theorem full_spectrum_Equation1682 : HasFullSpectrum [1682] := by
  intro n
  if h : n > 2 then
    let op (x y : Fin n) : Fin n := ⟨
      if y.1 = 0 then x.1
      else if y.1 = 1 then
        if x.1 = 0 then 1
        else 0
      else if (x.1 + y.1) % 2 = 0 then
        if x.1 ≥ 2 && y.1 ≥ 2 then
          if x.1 ≥ y.1 then x.1
          else x.1 + 1
        else if x.1 = 1 && y.1 ≥ 3 then y.1
        else 1
      else
        if x.1 ≥ 1 && y.1 ≥ 3 then
          if y.1 > x.1 then y.1
          else y.1 - 1
        else if x.1 = 1 && y.1 = 2 then 2
        else if x.1 = 0 && y.1 ≥ 3 then 2
        else 0,
      by
        repeat' split
        all_goals try simp [show 0 < n ∧ 1 < n ∧ 2 < n by omega]
        . simp [show x.1 + 1 < n by omega]
        . exact Nat.sub_one_lt_of_le (by omega) (by omega)
    ⟩
    use ⟨op⟩
    intro x y
    apply Fin.eq_mk_iff_val_eq.mpr
    have l₁ (x : Nat) : (x + x) % 2 = 0 := by omega
    have l₂ {n : Nat} (h : n ≥ 3) : n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n > 1 ∧ n > 2 ∧ n ≥ 1 ∧ n ≥ 2 ∧
      ¬n ≤ 2 ∧ ¬n < 2 ∧ ¬n < 3 ∧ (n - 1) ≥ 2 := by omega
    have l₃ {a b : Nat} (h : (a + b) % 2 = 0) : (b + a) % 2 = 0 ∧ (a + (b + 1)) % 2 = 1 ∧
      (b + 1 + a) % 2 ≠ 0 := by omega
    have t₁ (n : Nat) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n ≥ 3 := by omega
    rcases t₁ x.1 with h₁ | h₁ | h₁ | h₁ <;> rcases t₁ y.1 with h₂ | h₂ | h₂ | h₂
    all_goals simp [*]
    . rcases eq_or_ne (y.1 % 2) 0 with h₃ | h₃
      all_goals simp [*]
    . rcases eq_or_ne (y.1 % 2) 0 with h₃ | h₃
      all_goals simp [*]
    . rcases eq_or_ne (y.1 % 2) 0 with h₃ | h₃
      . simp [*]
      . simp [show y.1 % 2 = 1 by omega, *]
    . rcases eq_or_ne (x.1 % 2) 0 with h₃ | h₃
      all_goals simp [*]
    . rcases eq_or_ne (x.1 % 2) 0 with h₃ | h₃
      . simp [show (3 + ↑x) % 2 ≠ 0 ∧ x.1 > 3 by omega, *]
      . simp [show x.1 % 2 = 1 by omega, *]
    . rcases eq_or_ne ((x.1 + y.1) % 2) 0 with h₃ | h₃ <;>
        rcases (show x < y ∨ x = y ∨ x > y by omega) with h₄ | h₄ | h₄
      have l₄ {a b : Nat} (h : a > b) : a ≥ b ∧ b < a ∧ ¬a < b + 1 := by omega
      . simp [show ¬y ≤ x ∧ x ≤ y by omega, *]
      . simp [*]
      . simp [show y ≤ x ∧ ¬x ≤ y ∧ y.1 + 1 < x.1 by omega, *]
      all_goals have l₅ {a b : Nat} (h : (a + b) % 2 ≠ 0) : (b + a) % 2 = 1 ∧ (a + b) % 2 = 1 ∧
        (b + a) % 2 ≠ 0 := by omega
      . simp [show ¬y < x ∧ (x.1 - 1 + y.1) % 2 = 0 ∧ ¬y.1 ≤ (x.1 - 1) by omega, *]
      . simp [*]
      . simp [show (x.1 + (y.1 - 1)) % 2 = 0 ∧ ¬x < y ∧ y.1 ≤ x.1 + 1 by omega, *]
  else if h : n = 2 then
    let op (x y : Fin n) : Fin n := ⟨(x.1 + y.1) % 2, by omega⟩
    use ⟨op⟩
    simp only [Equation1682, op]
    intros
    apply Fin.eq_mk_iff_val_eq.mpr
    omega
  else
    use ⟨fun x y => x⟩
    omega

private lemma op_eq2 (_ : Magma (Fin 2)) (x y : Fin 2) : x ◇ y = 0 ∨ x ◇ y = 1 := by omega

theorem not_full_spectrum_card2_2var : NotFullSpectrum [66, 73, 118, 167, 467, 474, 501, 670, 677,
    704, 873, 907, 1076, 1083, 1110, 1279, 1286, 1313, 1489, 1516, 1685, 1692, 1719] := by
  repeat' apply And.intro
  all_goals {
    simp only [not_exists, not_forall]
    use 2
    intro m
    rcases (op_eq2 m 0 0) <;> rcases (op_eq2 m 0 1) <;> rcases (op_eq2 m 1 0) <;>
      rcases (op_eq2 m 1 1)
    all_goals try {
      try {
        use 1, 0
        simp only [zero_ne_one, one_ne_zero, not_false_eq_true, *]
      }
      try {
        use 0, 1
        simp only [zero_ne_one, one_ne_zero, not_false_eq_true, *]
      }
      try {
        use 0, 0
        simp only [zero_ne_one, one_ne_zero, not_false_eq_true, *]
      }
      try {
        use 1, 1
        simp only [zero_ne_one, one_ne_zero, not_false_eq_true, *]
      }
    }
  }

theorem not_full_spectrum_card2_3var : NotFullSpectrum [1480, 1486] := by
  repeat' apply And.intro
  all_goals {
    simp only [not_exists, not_forall]
    use 2
    intro m
    rcases (op_eq2 m 0 0) <;> rcases (op_eq2 m 0 1) <;> rcases (op_eq2 m 1 0) <;>
      rcases (op_eq2 m 1 1)
    all_goals {
      try {
        use 1, 0, 0
        simp only [zero_ne_one, one_ne_zero, not_false_eq_true, *]
      }
      try {
        use 0, 1, 0
        simp only [zero_ne_one, one_ne_zero, not_false_eq_true, *]
      }
      try {
        use 1, 0, 1
        simp only [zero_ne_one, one_ne_zero, not_false_eq_true, *]
      }
    }
  }

end FullSpectrum
