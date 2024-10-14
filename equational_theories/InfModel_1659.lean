import equational_theories.Equations.All
import equational_theories.MagmaOp
import Aesop
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import equational_theories.Mathlib.Algebra.Group.Nat

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
theorem Equation1659_not_implies_Equation4315 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation4315 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 0, 1


@[equational_result]
theorem Equation1659_not_implies_Equation4314 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation4314 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 1, 0

@[equational_result]
theorem Equation1659_not_implies_Equation4268 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation4268 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1

@[equational_result]
theorem Equation1659_not_implies_Equation3527 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation3527 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 0, 1, 0


@[equational_result]
theorem Equation1659_not_implies_Equation3525 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation3525 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 0, 1


@[equational_result]
theorem Equation1659_not_implies_Equation3524 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation3524 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 0, 1

@[equational_result]
theorem Equation1659_not_implies_Equation3520 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation3520 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1, 1


@[equational_result]
theorem Equation1659_not_implies_Equation3519 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation3519 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1

@[equational_result]
theorem Equation1659_not_implies_Equation3460 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation3460 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1, 0


@[equational_result]
theorem Equation1659_not_implies_Equation3458 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation3458 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 1, 0

@[equational_result]
theorem Equation1659_not_implies_Equation2460 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation2460 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1

@[equational_result]
theorem Equation1659_not_implies_Equation2452 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation2452 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1, 0


@[equational_result]
theorem Equation1659_not_implies_Equation2446 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation2446 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1

@[equational_result]
theorem Equation1659_not_implies_Equation1860 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation1860 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 1, 0


@[equational_result]
theorem Equation1659_not_implies_Equation1851 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation1851 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 1, 0

@[equational_result]
theorem Equation1659_not_implies_Equation1839 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation1839 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1, 0


@[equational_result]
theorem Equation1659_not_implies_Equation1837 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation1837 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1

@[equational_result]
theorem Equation1659_not_implies_Equation1833 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation1833 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1



@[equational_result]
theorem Equation1659_not_implies_Equation1661 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation1661 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1, 0


@[equational_result]
theorem Equation1659_not_implies_Equation1660 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation1660 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 1, 1, 0


@[equational_result]
theorem Equation1659_not_implies_Equation1656 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation1656 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1, 1


@[equational_result]
theorem Equation1659_not_implies_Equation1655 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation1655 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1

@[equational_result]
theorem Equation1659_not_implies_Equation1631 :
  ∃ (G : Type) (_ : Magma G), Equation1659 G ∧ ¬ Equation1631 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1659_4315 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation3253,magN,op]
  apply And.intro
  · exact op_1659_4315_satisfies_1659
  exists 0, 1
