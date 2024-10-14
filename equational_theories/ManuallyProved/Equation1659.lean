import equational_theories.Equations.All
import equational_theories.MagmaOp
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import equational_theories.Mathlib.Algebra.Group.Nat
import equational_theories.FactsSyntax

/-
  We build an infinite model of 1659 which does not satisfy 4315.
-/


private theorem mod_two_succ_0_1_from (n : ℕ) : n % 2 = 0 → (n + 1) % 2 = 1 := by omega
private theorem mod_two_succ_1_0_from (n : ℕ) : n % 2 = 1 → (n + 1) % 2 = 0 := by omega
private theorem mod_two_pred_0_1_to (n : ℕ) : (n + 1) % 2 = 0 → n % 2 = 1 := by omega
private theorem mod_two_pred_1_0_to (n : ℕ) : (n + 1) % 2 = 1 → n % 2 = 0 := by omega
private theorem mod_two_ne_down_to (n m : ℕ) : (n + 1) % 2 = m % 2 → ¬ n % 2 = m % 2 := by omega
private theorem mod_two_eq_down_to (n m : ℕ) : (n + 1) % 2 ≠ m % 2 → n % 2 = m % 2 := by omega
private theorem mod_two_ne_up_from (n m : ℕ) : n % 2 = m % 2 → ¬ (n + 1) % 2 = m % 2 := by omega
private theorem mod_two_eq_up_from (n m : ℕ) : n % 2 ≠ m % 2 → (n + 1) % 2 = m % 2 := by omega

private def op_1659_4315 (x : ℕ) (y : ℕ) : ℕ :=
  match x with
  | 0 =>
    if y % 2 = 0
    then 1 else 0
  | n + 1 =>
    if x % 2 = y % 2
    then n + 2 else n

private theorem op_1659_4315_satisfies_1659 :
  ∀ (x y z : ℕ),
  x = op_1659_4315 (op_1659_4315 x y) (op_1659_4315 (op_1659_4315 y y) z ) := by
  intro xo yo z
  by_cases z_cong_0 : z % 2 = 0
  · match xo, yo with
    | 0, 0 =>
      simp [op_1659_4315]
      split
      · simp
      · simp
    | 0, y+1 =>
      simp [op_1659_4315]
      by_cases y1_cong_0 : (y + 1) % 2 = 0
      · have y_cong_1 : y % 2  = 1 :=
          mod_two_pred_0_1_to y y1_cong_0
        simp [op_1659_4315,y1_cong_0,y_cong_1,z_cong_0]
      · have y1_cong_1 : (y + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp y1_cong_0
        have y_cong_0 : y % 2 = 0 :=
          mod_two_pred_1_0_to y y1_cong_1
        simp [op_1659_4315,y1_cong_0,y_cong_0,z_cong_0]
    | x+1, 0 =>
      simp [op_1659_4315]
      by_cases x1_cong_0 : (x + 1) % 2 = 0
      · have x_cong_1 : x % 2  = 1 :=
          mod_two_pred_0_1_to x x1_cong_0
        simp [op_1659_4315,x1_cong_0,x_cong_1,z_cong_0]
      · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
        have x_cong_0 : x % 2 = 0 :=
          mod_two_pred_1_0_to x x1_cong_1
        simp [op_1659_4315,x1_cong_0,x_cong_0,z_cong_0]
        split
        simp_all only [zero_add, one_ne_zero, not_false_eq_true, Nat.mod_succ, Nat.zero_mod]
        simp
    | x+1, y+1 =>
      by_cases y1_cong_0 : (y + 1) % 2 = 0
      · have y_cong_1 : y % 2  = 1 :=
          mod_two_pred_0_1_to y y1_cong_0
        by_cases x1_cong_0 : (x + 1) % 2 = 0
        · have x_cong_1 : x % 2  = 1 :=
            mod_two_pred_0_1_to x x1_cong_0
          simp [op_1659_4315,y1_cong_0,y_cong_1,x1_cong_0,x_cong_1,z_cong_0]
        · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
          have x_cong_0 : x % 2  = 0 :=
            mod_two_pred_1_0_to x x1_cong_1
          simp [op_1659_4315,y1_cong_0,y_cong_1,x1_cong_0,x_cong_0,z_cong_0]
          split
          simp
          simp
      · have y1_cong_1 : (y + 1) % 2 = 1 :=
          Nat.mod_two_ne_zero.mp y1_cong_0
        have y_cong_0 : y % 2 = 0 :=
          mod_two_pred_1_0_to y y1_cong_1
        by_cases x1_cong_0 : (x + 1) % 2 = 0
        · have x_cong_1 : x % 2  = 1 :=
            mod_two_pred_0_1_to x x1_cong_0
          simp [op_1659_4315,x1_cong_0,y1_cong_1,y_cong_0,z_cong_0,x_cong_1]
          split
          simp_all only [one_ne_zero, not_false_eq_true, zero_add, Nat.mod_succ]
          simp
        · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
          have x_cong_0 : x % 2  = 0 :=
            mod_two_pred_1_0_to x x1_cong_1
          simp [op_1659_4315,y1_cong_0,y_cong_0,x1_cong_1,y1_cong_1,x_cong_0,z_cong_0]
  · have z_cong_1 : z % 2 = 1 :=
      Nat.mod_two_ne_zero.mp z_cong_0
    match xo, yo with
    | 0, 0 =>
      simp [op_1659_4315]
      split
      · simp
      · simp
    | 0, y+1 =>
      simp [op_1659_4315]
      by_cases y1_cong_0 : (y + 1) % 2 = 0
      · have y_cong_1 : y % 2  = 1 :=
          mod_two_pred_0_1_to y y1_cong_0
        simp [op_1659_4315,y1_cong_0,y_cong_1,z_cong_1]
      · have y1_cong_1 : (y + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp y1_cong_0
        have y_cong_0 : y % 2 = 0 :=
          mod_two_pred_1_0_to y y1_cong_1
        simp [op_1659_4315,y1_cong_0,y_cong_0,z_cong_1]
    | x+1, 0 =>
      simp [op_1659_4315]
      by_cases x1_cong_0 : (x + 1) % 2 = 0
      · have x_cong_1 : x % 2  = 1 :=
          mod_two_pred_0_1_to x x1_cong_0
        simp [op_1659_4315,x1_cong_0,x_cong_1,z_cong_1]
      · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
        have x_cong_0 : x % 2 = 0 :=
          mod_two_pred_1_0_to x x1_cong_1
        simp [op_1659_4315,x1_cong_0,x_cong_0,z_cong_1]
        split
        simp_all only [zero_add, one_ne_zero, not_false_eq_true, Nat.mod_succ, Nat.zero_mod]
        simp
    | x+1, y+1 =>
      by_cases y1_cong_0 : (y + 1) % 2 = 0
      · have y_cong_1 : y % 2  = 1 :=
          mod_two_pred_0_1_to y y1_cong_0
        by_cases x1_cong_0 : (x + 1) % 2 = 0
        · have x_cong_1 : x % 2  = 1 :=
            mod_two_pred_0_1_to x x1_cong_0
          simp [op_1659_4315,y1_cong_0,y_cong_1,x1_cong_0,x_cong_1,z_cong_1]
        · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
          have x_cong_0 : x % 2  = 0 :=
            mod_two_pred_1_0_to x x1_cong_1
          simp [op_1659_4315,y1_cong_0,y_cong_1,x1_cong_0,x_cong_0,z_cong_1]
          split
          simp
          simp
      · have y1_cong_1 : (y + 1) % 2 = 1 :=
          Nat.mod_two_ne_zero.mp y1_cong_0
        have y_cong_0 : y % 2 = 0 :=
          mod_two_pred_1_0_to y y1_cong_1
        by_cases x1_cong_0 : (x + 1) % 2 = 0
        · have x_cong_1 : x % 2  = 1 :=
            mod_two_pred_0_1_to x x1_cong_0
          simp [op_1659_4315,x1_cong_0,y1_cong_1,y_cong_0,z_cong_1,x_cong_1]
          split
          simp_all only [one_ne_zero, not_false_eq_true, zero_add, Nat.mod_succ]
          simp
        · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
          have x_cong_0 : x % 2  = 0 :=
            mod_two_pred_1_0_to x x1_cong_1
          simp [op_1659_4315,y1_cong_0,y_cong_0,x1_cong_1,y1_cong_1,x_cong_0,z_cong_1]

@[equational_result]
theorem Equation1659_facts :
  ∃ (G : Type) (_ : Magma G), Facts G [1659]
    [1631,1655,1656,1660,1661,1833,1837,1839,1851,1860,2446,2452,2460,3458,3460,3519,3520,3524,3525,3527,4268,4314,4315] := by
  let magN : Magma ℕ := { op := op_1659_4315 }
  use ℕ, magN

  constructor
  · simp only [magN]
    exact op_1659_4315_satisfies_1659
  · repeat' apply And.intro
    all_goals {
      by_contra h
      have h1 := h
      have h2 := h
      try specialize h 0 0 1 0
      try specialize h 0 0 1
      try specialize h1 0 1 0
      try specialize h2 0 1 1
      try specialize h 0 1
      try specialize h1 1 0
      try simp [magN,op_1659_4315] at h
      try simp [magN,op_1659_4315] at h1
      try simp [magN,op_1659_4315] at h2
    }
