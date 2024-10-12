import equational_theories.Equations.All
import equational_theories.MagmaOp
import Aesop
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import equational_theories.Mathlib.Algebra.Group.Nat

/- Infinite models showing anti-implications 1661 → ⋯ -/

/- Equation1661_not_implies_Equation1657 -/

/-!
  op_1661_1657 is obtained by starting with
          { x - 1    if x and y have the same parity
  x # y = |
          { x + 1    if x and y have opposite parities
  on the integers. This operation satisfies 1661.
  The # operation is truncated to the nonnegatives, and
  "patched up" around zero so as to break equation 1657
  while retaining 1661.
-/
private def op_1661_1657 (x : ℕ) (y : ℕ) : ℕ :=
  match x with
  | 0 => if y % 2 = 0 then 0 else 2
  | 1 => if y % 2 = 0 then 1 else 3
  | 2 => if y % 2 = 0 then 2 else 0
  | 3 => if y % 2 = 0 then 4 else 1
  | n + 4 =>
    if x % 2 = y % 2
    then n + 3 else n + 5

/-
  The bulk of the proof is verifying that the patch-up retains equation 1661.
  This has to be done by a case analysis both on the patched cases and the rest
  of the numbers modulo 2. Having the following theorems for manipulating values
  mod 2 makes the proof more readable. We write them as private theorems since
  putting them inside the "have" leads to timeouts in the large case analyses.
-/

private theorem mod_two_succ_0_1_from (n : ℕ) : n % 2 = 0 → (n + 1) % 2 = 1 := by omega

private theorem mod_two_succ_1_0_from (n : ℕ) : n % 2 = 1 → (n + 1) % 2 = 0 := by omega

private theorem mod_two_pred_0_1_to (n : ℕ) : (n + 1) % 2 = 0 → n % 2 = 1 := by omega

private theorem mod_two_pred_1_0_to (n : ℕ) : (n + 1) % 2 = 1 → n % 2 = 0 := by omega

private theorem mod_two_ne_down_to (n m : ℕ) : (n + 1) % 2 = m % 2 → ¬ n % 2 = m % 2 := by omega

private theorem mod_two_eq_down_to (n m : ℕ) : (n + 1) % 2 ≠ m % 2 → n % 2 = m % 2 := by omega

private theorem mod_two_ne_up_from (n m : ℕ) : n % 2 = m % 2 → ¬ (n + 1) % 2 = m % 2 := by omega

private theorem mod_two_eq_up_from (n m : ℕ) : n % 2 ≠ m % 2 → (n + 1) % 2 = m % 2 := by omega

/-
  We prove lemmata about the left (x ⋄ y) and the right ((y ⋄ z) ⋄ y) of
  equation 1661's right-hand side. These will be used in rewrites to avoid simp
  creating extremely large terms in the proof below.
-/

private def delta_right_even (n : ℕ) : ℕ :=
  match n with
    | 0 => 5
    | 1 => 7
    | 2 => 5
    | 3 => 7
    | 4 => 5
    | n+5 => if (n + 5) % 2 = 0 then 5 else 7

private theorem op_right_even (y : ℕ) : (y + 5) % 2 = 0 → ∀ (x : ℕ), op_1661_1657 (op_1661_1657 (y + 5) x) (y + 5) = y + delta_right_even x := by
    intro y5e x
    have y4o : (y + 4) % 2 = 1 := Nat.succ_mod_two_eq_zero_iff.mp y5e
    have y6o : (y + 6) % 2 = 1 := Nat.succ_mod_two_eq_one_iff.mpr y5e
    match x with
    | 0 | 1 | 2 | 3 | 4 => simp [op_1661_1657,y5e,y4o,y6o,delta_right_even]
    | n+5 =>
      by_cases n5eo : (n + 5) % 2 = 0
      · simp [op_1661_1657, y5e, n5eo, y4o, delta_right_even]
      · simp [op_1661_1657, y5e, y6o, Nat.mod_two_ne_zero.mp n5eo, delta_right_even]

private def delta_right_odd (n : ℕ) : ℕ :=
    match n with
    | 0 => 7
    | 1 => 5
    | 2 => 7
    | 3 => 5
    | 4 => 7
    | n+5 => if (n + 5) % 2 = 0 then 7 else 5

private theorem op_right_odd (y : ℕ) : (y + 5) % 2 ≠ 0 → ∀ (x : ℕ), op_1661_1657 (op_1661_1657 (y + 5) x) (y + 5) = y + delta_right_odd x := by
    intro y5o x
    have y5o' : (y + 5) % 2 = 1 := by
      simp_all only [↓reduceIte, ne_eq, Nat.mod_two_ne_zero]
    have y4e : (y + 4) % 2 = 0 := Nat.succ_mod_two_eq_one_iff.mp y5o'
    have y6e : (y + 6) % 2 = 0 := by omega
    match x with
    | 0 | 1 | 2 | 3 | 4 =>
      simp [op_1661_1657,y5o',y4e,y6e,delta_right_odd]
    | n+5 =>
      by_cases n5eo : (n + 5) % 2 = 0
      · simp [op_1661_1657, y5o', n5eo, y4e, y6e, delta_right_odd]
      · simp [op_1661_1657, y5o', Nat.mod_two_ne_zero.mp n5eo, y4e, delta_right_odd]

private theorem op_left_eq (x y : ℕ) : (x + 5) % 2 = (y + 5) % 2 → op_1661_1657 (x + 5) (y + 5) = x + 4 := by
  simp [op_1661_1657]

private theorem op_left_ne (x y : ℕ) : ¬ ((x + 5) % 2 = (y + 5) % 2) → op_1661_1657 (x + 5) (y + 5) = x + 6 := by
  simp [op_1661_1657]

private theorem op_right_eq (y z : ℕ) : (y + 5) % 2 = (z + 5) % 2 → op_1661_1657 (op_1661_1657 (y + 5) (z + 5)) (y + 5) = y + 5 := by
  intro yz5
  simp [op_1661_1657,yz5, mod_two_ne_down_to _ _ yz5]

private theorem op_right_ne (y z : ℕ) : ¬ (y + 5) % 2 = (z + 5) % 2 → op_1661_1657 (op_1661_1657 (y + 5) (z + 5)) (y + 5) = y + 7 := by
  intro yz5
  simp [op_1661_1657,yz5]
  have r : (y + 5) % 2 = (y + 5) % 2 := by simp
  exact (mod_two_ne_up_from _ _ r)


/-
  Now we're ready to prove that 1661 holds in the magma constructed above.
  This has to be done by a case analysis both on the patched cases and the rest of
  the numbers modulo 2. Most of this is routine w/ the lemmata proven above. The cases
  that require some care are the ones that involve two non-exceptional numbers and one exceptional
  number. These are handled at the end.

  Keep in mind that the exceptional numbers are 0,1,2,3,4, not just the 0,1,2,3
  that we match on.
-/


private theorem op_1661_1657_satisfies_1661 :
  ∀ x y z : ℕ, x = op_1661_1657 (op_1661_1657 x y) (op_1661_1657 (op_1661_1657 y z) y) := by
  intro xo yo zo
  match xo,yo,zo with
  | 0, 0, 0 | 0, 0, 1 | 0, 0, 2 | 0, 0, 3 | 0, 0, 4
  | 0, 1, 0 | 0, 1, 1 | 0, 1, 2 | 0, 1, 3 | 0, 1, 4
  | 0, 2, 0 | 0, 2, 1 | 0, 2, 2 | 0, 2, 3 | 0, 2, 4
  | 0, 3, 0 | 0, 3, 1 | 0, 3, 2 | 0, 3, 3 | 0, 3, 4
  | 0, 4, 0 | 0, 4, 1 | 0, 4, 2 | 0, 4, 3 | 0, 4, 4
  | 1, 0, 0 | 1, 0, 1 | 1, 0, 2 | 1, 0, 3 | 1, 0, 4
  | 1, 1, 0 | 1, 1, 1 | 1, 1, 2 | 1, 1, 3 | 1, 1, 4
  | 1, 2, 0 | 1, 2, 1 | 1, 2, 2 | 1, 2, 3 | 1, 2, 4
  | 1, 3, 0 | 1, 3, 1 | 1, 3, 2 | 1, 3, 3 | 1, 3, 4
  | 1, 4, 0 | 1, 4, 1 | 1, 4, 2 | 1, 4, 3 | 1, 4, 4
  | 2, 0, 0 | 2, 0, 1 | 2, 0, 2 | 2, 0, 3 | 2, 0, 4
  | 2, 1, 0 | 2, 1, 1 | 2, 1, 2 | 2, 1, 3 | 2, 1, 4
  | 2, 2, 0 | 2, 2, 1 | 2, 2, 2 | 2, 2, 3 | 2, 2, 4
  | 2, 3, 0 | 2, 3, 1 | 2, 3, 2 | 2, 3, 3 | 2, 3, 4
  | 2, 4, 0 | 2, 4, 1 | 2, 4, 2 | 2, 4, 3 | 2, 4, 4
  | 3, 0, 0 | 3, 0, 1 | 3, 0, 2 | 3, 0, 3 | 3, 0, 4
  | 3, 1, 0 | 3, 1, 1 | 3, 1, 2 | 3, 1, 3 | 3, 1, 4
  | 3, 2, 0 | 3, 2, 1 | 3, 2, 2 | 3, 2, 3 | 3, 2, 4
  | 3, 3, 0 | 3, 3, 1 | 3, 3, 2 | 3, 3, 3 | 3, 3, 4
  | 3, 4, 0 | 3, 4, 1 | 3, 4, 2 | 3, 4, 3 | 3, 4, 4
  | 4, 0, 0 | 4, 0, 1 | 4, 0, 2 | 4, 0, 3 | 4, 0, 4
  | 4, 1, 0 | 4, 1, 1 | 4, 1, 2 | 4, 1, 3 | 4, 1, 4
  | 4, 2, 0 | 4, 2, 1 | 4, 2, 2 | 4, 2, 3 | 4, 2, 4
  | 4, 3, 0 | 4, 3, 1 | 4, 3, 2 | 4, 3, 3 | 4, 3, 4
  | 4, 4, 0 | 4, 4, 1 | 4, 4, 2 | 4, 4, 3 | 4, 4, 4 =>
    simp [op_1661_1657]

  | x+5, 0, 0 | x+5, 0, 1 | x+5, 0, 2 | x+5, 0, 3 | x+5, 0, 4
  | x+5, 1, 0 | x+5, 1, 1 | x+5, 1, 2 | x+5, 1, 3 | x+5, 1, 4
  | x+5, 2, 0 | x+5, 2, 1 | x+5, 2, 2 | x+5, 2, 3 | x+5, 2, 4
  | x+5, 3, 0 | x+5, 3, 1 | x+5, 3, 2 | x+5, 3, 3 | x+5, 3, 4
  | x+5, 4, 0 | x+5, 4, 1 | x+5, 4, 2 | x+5, 4, 3 | x+5, 4, 4
  | 0, x+5, 0 | 0, x+5, 1 | 0, x+5, 2 | 0, x+5, 3 | 0, x+5, 4
  | 1, x+5, 0 | 1, x+5, 1 | 1, x+5, 2 | 1, x+5, 3 | 1, x+5, 4
  | 2, x+5, 0 | 2, x+5, 1 | 2, x+5, 2 | 2, x+5, 3 | 2, x+5, 4
  | 3, x+5, 0 | 3, x+5, 1 | 3, x+5, 2 | 3, x+5, 3 | 3, x+5, 4
  | 4, x+5, 0 | 4, x+5, 1 | 4, x+5, 2 | 4, x+5, 3 | 4, x+5, 4
  | 0, 0, x+5 | 0, 1, x+5 | 0, 2, x+5 | 0, 3, x+5 | 0, 4, x+5
  | 1, 0, x+5 | 1, 1, x+5 | 1, 2, x+5 | 1, 3, x+5 | 1, 4, x+5
  | 2, 0, x+5 | 2, 1, x+5 | 2, 2, x+5 | 2, 3, x+5 | 2, 4, x+5
  | 3, 0, x+5 | 3, 1, x+5 | 3, 2, x+5 | 3, 3, x+5 | 3, 4, x+5
  | 4, 0, x+5 | 4, 1, x+5 | 4, 2, x+5 | 4, 3, x+5 | 4, 4, x+5 =>
    simp [op_1661_1657]
    by_cases hx5 : (x + 5) % 2 = 0
    · have hx4 : (x + 4) % 2 = 1 :=
        mod_two_pred_0_1_to (x + 4) hx5
      have hx6 : (x + 6) % 2 = 1 :=
        mod_two_succ_0_1_from (x + 5) hx5
      have hx7 : (x + 7) % 2 = 0 :=
        mod_two_succ_1_0_from (x + 6) hx6
      simp [hx4, hx5, hx6, hx7]
    · have hx5' : (x + 5) % 2 = 1 :=
        Nat.mod_two_ne_zero.mp hx5
      have hx4' : (x + 4) % 2 = 0 :=
        mod_two_pred_1_0_to (x + 4) hx5'
      have hx6' : (x + 6) % 2 = 0 :=
        mod_two_succ_1_0_from (x + 5) hx5'
      have hx7' : (x + 7) % 2 = 1 :=
        mod_two_succ_0_1_from (x + 6) hx6'
      simp [hx4', hx5', hx6', hx7']

  | x+5, y+5, z+5 =>
    by_cases hyz5 : (y + 5) % 2 = (z + 5) % 2
    · rw [op_right_eq y z hyz5]
      by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
      · rw [op_left_eq x y hxy5]
        have hxy4 : ¬ (x + 4) % 2 = (y + 5) % 2 :=
          mod_two_ne_down_to (x + 4) (y + 5) hxy5
        simp [op_1661_1657,hxy4]
      · rw [op_left_ne x y hxy5]
        have hxy6 : (x + 6) % 2 = (y + 5) % 2 :=
          mod_two_eq_up_from (x + 5) (y + 5) hxy5
        simp [op_1661_1657,hxy6]
    · rw [op_right_ne y z hyz5]
      by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
      · rw [op_left_eq x y hxy5]
        have hxy45 : (x + 4) % 2 ≠ (y + 5) % 2 :=
          mod_two_ne_down_to (x + 4) (y + 5) hxy5
        have hxy46 : (y + 6) % 2 = (x + 4) % 2 :=
          mod_two_eq_up_from (y + 5) (x + 4) (Ne.symm hxy45)
        have hxy43 : ¬ (x + 4) % 2 = (y + 7) % 2 :=
          Ne.symm (mod_two_ne_up_from (y + 6) (x + 4) hxy46)
        simp [op_1661_1657,hxy43]
      · rw [op_left_ne x y hxy5]
        simp [op_1661_1657,]
        have hxy56 : (x + 6) % 2 = (y + 5) % 2 := mod_two_eq_up_from (x + 5) (y + 5) hxy5
        have hxy6 : (y + 6) % 2 ≠ (x + 6) % 2 := mod_two_ne_up_from (y + 5) (x + 6) hxy56.symm
        have hxy67 : (x + 6) % 2 = (y + 7) % 2 := (mod_two_eq_up_from (y + 6) (x + 6) hxy6).symm
        simp [op_1661_1657,hxy67]

  | x+5, y+5, 0 =>  -- also 2,4
    by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
    · rw [op_left_eq x y hxy5]
      by_cases h5 : (y + 5) % 2 = 0
      · rw [op_right_even y h5 0]
        simp only [delta_right_even]
        have hxy45 : ¬ (x + 4) % 2 = (y + 5) % 2 :=
          mod_two_ne_down_to (x + 4) (y + 5) hxy5
        simp [op_1661_1657,hxy45]
      · rw [op_right_odd y h5 0]
        simp only [delta_right_odd]
        have hxy56 : (y + 6) % 2 ≠ (x + 5) % 2 := mod_two_ne_up_from (y + 5) (x + 5) hxy5.symm
        have hxy57 : (x + 5) % 2 = (y + 7) % 2 := (mod_two_eq_up_from (y + 6) (x + 5) hxy56).symm
        have hxy47 : ¬ (x + 4) % 2 = (y + 7) % 2 :=
          mod_two_ne_down_to (x + 4) (y +7) hxy57
        simp [op_1661_1657,hxy47]
    · rw [op_left_ne x y hxy5]
      by_cases h5 : (y + 5) % 2 = 0
      · rw [op_right_even y h5 0]
        simp only [delta_right_even]
        have hxy65 : (x + 6) % 2 = (y + 5) % 2 :=
          mod_two_eq_up_from (x + 5) (y + 5) hxy5
        rw [op_left_eq (x+1) y]
        exact hxy65
      · rw [op_right_odd y h5 0]
        simp only [delta_right_odd]
        have hxy56 : (y + 6) % 2 = (x + 5) % 2 := mod_two_eq_up_from (y + 5) (x + 5) (Ne.symm hxy5)
        have hxy57 : (y + 7) % 2 ≠ (x + 5) % 2 := mod_two_ne_up_from (y + 6) (x + 5) hxy56
        have hxy67 : (x + 6) % 2 = (y + 7) % 2 := mod_two_eq_up_from (x + 5) (y + 7) (Ne.symm hxy57)
        simp [op_1661_1657,hxy67]

  | x+5, y+5, 2 =>  -- also 0,4
    by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
    · rw [op_left_eq x y hxy5]
      by_cases h5 : (y + 5) % 2 = 0
      · rw [op_right_even y h5 2]
        simp only [delta_right_even]
        have hxy45 : ¬ (x + 4) % 2 = (y + 5) % 2 :=
          mod_two_ne_down_to (x + 4) (y + 5) hxy5
        simp [op_1661_1657,hxy45]
      · rw [op_right_odd y h5 2]
        simp only [delta_right_odd]
        have hxy56 : (y + 6) % 2 ≠ (x + 5) % 2 := mod_two_ne_up_from (y + 5) (x + 5) hxy5.symm
        have hxy57 : (x + 5) % 2 = (y + 7) % 2 := (mod_two_eq_up_from (y + 6) (x + 5) hxy56).symm
        have hxy47 : ¬ (x + 4) % 2 = (y + 7) % 2 := mod_two_ne_down_to (x + 4) (y +7) hxy57
        simp [op_1661_1657,hxy47]
    · rw [op_left_ne x y hxy5]
      by_cases h5 : (y + 5) % 2 = 0
      · rw [op_right_even y h5 2]
        simp only [delta_right_even]
        have hxy65 : (x + 6) % 2 = (y + 5) % 2 := mod_two_eq_up_from (x + 5) (y + 5) hxy5
        rw [op_left_eq (x+1) y]
        exact hxy65
      · rw [op_right_odd y h5 2]
        simp only [delta_right_odd]
        have hxy56 : (y + 6) % 2 = (x + 5) % 2 := mod_two_eq_up_from (y + 5) (x + 5) (Ne.symm hxy5)
        have hxy57 : (y + 7) % 2 ≠ (x + 5) % 2 := mod_two_ne_up_from (y + 6) (x + 5) hxy56
        have hxy67 : (x + 6) % 2 = (y + 7) % 2 := mod_two_eq_up_from (x + 5) (y + 7) (Ne.symm hxy57)
        simp [op_1661_1657,hxy67]

  | x+5, y+5, 4 =>  -- also 0,2
    by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
    · rw [op_left_eq x y hxy5]
      by_cases h5 : (y + 5) % 2 = 0
      · rw [op_right_even y h5 4]
        simp only [delta_right_even]
        have hxy45 : ¬ (x + 4) % 2 = (y + 5) % 2 :=
          mod_two_ne_down_to (x + 4) (y + 5) hxy5
        simp [op_1661_1657,hxy45]
      · rw [op_right_odd y h5 4]
        simp only [delta_right_odd]
        have hxy56 : (y + 6) % 2 ≠ (x + 5) % 2 := mod_two_ne_up_from (y + 5) (x + 5) hxy5.symm
        have hxy57 : (x + 5) % 2 = (y + 7) % 2 := (mod_two_eq_up_from (y + 6) (x + 5) hxy56).symm
        have hxy47 : ¬ (x + 4) % 2 = (y + 7) % 2 := mod_two_ne_down_to (x + 4) (y +7) hxy57
        simp [op_1661_1657,hxy47]
    · rw [op_left_ne x y hxy5]
      by_cases h5 : (y + 5) % 2 = 0
      · rw [op_right_even y h5 4]
        simp only [delta_right_even]
        have hxy65 : (x + 6) % 2 = (y + 5) % 2 :=
          mod_two_eq_up_from (x + 5) (y + 5) hxy5
        rw [op_left_eq (x+1) y]
        exact hxy65
      · rw [op_right_odd y h5 4]
        simp only [delta_right_odd]
        have hxy56 : (y + 6) % 2 = (x + 5) % 2 := mod_two_eq_up_from (y + 5) (x + 5) (Ne.symm hxy5)
        have hxy57 : (y + 7) % 2 ≠ (x + 5) % 2 := mod_two_ne_up_from (y + 6) (x + 5) hxy56
        have hxy67 : (x + 6) % 2 = (y + 7) % 2 := mod_two_eq_up_from (x + 5) (y + 7) (Ne.symm hxy57)
        simp [op_1661_1657,hxy67]

  | x+5, y+5, 1 =>  -- also 3
    by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
    · rw [op_left_eq x y hxy5]
      by_cases h5 : (y + 5) % 2 = 0
      · rw [op_right_even y h5 1]
        simp only [delta_right_even]
        have hxy56 : (y + 6) % 2 ≠ (x + 5) % 2 := mod_two_ne_up_from (y + 5) (x + 5) hxy5.symm
        have hxy57 : (x + 5) % 2 = (y + 7) % 2 := (mod_two_eq_up_from (y + 6) (x + 5) hxy56).symm
        have hxy47 : ¬ (x + 4) % 2 = (y + 7) % 2 := mod_two_ne_down_to (x + 4) (y +7) hxy57
        simp [op_1661_1657,hxy47]
      · rw [op_right_odd y h5 1]
        simp only [delta_right_odd]
        have hxy45 : (x + 4) % 2 ≠ (y + 5) % 2 :=
          mod_two_ne_down_to (x + 4) (y + 5) hxy5
        simp [op_1661_1657,hxy5,hxy45]
    · rw [op_left_ne x y hxy5]
      by_cases h5 : (y + 5) % 2 = 0
      · rw [op_right_even y h5 1]
        simp only [delta_right_even]
        have hxy56 : (y + 6) % 2 = (x + 5) % 2 :=
          mod_two_eq_up_from (y + 5) (x + 5) (Ne.symm hxy5)
        have hxy57 : (y + 7) % 2 ≠ (x + 5) % 2 :=
          mod_two_ne_up_from (y + 6) (x + 5) hxy56
        have hxy67 : (x + 6) % 2 = (y + 7) % 2 :=
          mod_two_eq_up_from (x + 5) (y + 7) (Ne.symm hxy57)
        rw [op_left_eq (x+1) (y+2) hxy67]
      · rw [op_right_odd y h5 1]
        simp only [delta_right_odd]
        have hxy56 : (x + 6) % 2 = (y + 5) % 2 :=
          mod_two_eq_up_from (x + 5) (y + 5) hxy5
        simp [op_1661_1657,hxy56]

  | x+5, y+5, 3 =>  -- also 1
    by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
    · rw [op_left_eq x y hxy5]
      by_cases h5 : (y + 5) % 2 = 0
      · rw [op_right_even y h5 3]
        simp only [delta_right_even]
        have hxy56 : (y + 6) % 2 ≠ (x + 5) % 2 := mod_two_ne_up_from _ _ hxy5.symm
        have hxy57 : (x + 5) % 2 = (y + 7) % 2 := (mod_two_eq_up_from _ _ hxy56).symm
        have hxy47 : ¬ (x + 4) % 2 = (y + 7) % 2 :=
          mod_two_ne_down_to (x + 4) (y +7) hxy57
        simp [op_1661_1657,hxy47]
      · rw [op_right_odd y h5 3]
        simp only [delta_right_odd]
        have hxy45 : (x + 4) % 2 ≠ (y + 5) % 2 :=
          mod_two_ne_down_to (x + 4) (y + 5) hxy5
        simp [op_1661_1657,hxy5,hxy45]
    · rw [op_left_ne x y hxy5]
      by_cases h5 : (y + 5) % 2 = 0
      · rw [op_right_even y h5 3]
        simp only [delta_right_even]
        have hxy56 : (y + 6) % 2 = (x + 5) % 2 := mod_two_eq_up_from _ _ (Ne.symm hxy5)
        have hxy57 : (y + 7) % 2 ≠ (x + 5) % 2 := mod_two_ne_up_from _ _ hxy56
        have hxy67 : (x + 6) % 2 = (y + 7) % 2 := mod_two_eq_up_from _ _ (Ne.symm hxy57)
        rw [op_left_eq (x+1) (y+2) hxy67]
      · rw [op_right_odd y h5 3]
        simp only [delta_right_odd]
        have hxy56 : (x + 6) % 2 = (y + 5) % 2 :=
          mod_two_eq_up_from (x + 5) (y + 5) hxy5
        simp [op_1661_1657,hxy56]

  | x+5, 0, y+5 | x+5, 1, y+5 | x+5, 2, y+5 | x+5, 3, y+5 | x+5, 4, y+5 =>
    by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
    · by_cases h5y: (y + 5) % 2 = 0
      · have h5x : (x + 5) % 2 = 0 := by
          rw [hxy5]
          exact h5y
        have h4x : (x + 4) % 2 = 1 :=
          mod_two_pred_0_1_to (x + 4) h5x
        have h6x : (x + 6) % 2 = 1 :=
          mod_two_succ_0_1_from (x + 5) h5x
        simp [op_1661_1657,h5y]
        simp [h4x,h5x,h6x]
      · have h5y' : (y + 5) % 2 = 1 :=
          Nat.mod_two_ne_zero.mp h5y
        have h5x : (x + 5) % 2 = 1 := by
          rw [hxy5]
          exact h5y'
        have h4x : (x + 4) % 2 = 0 :=
          mod_two_pred_1_0_to (x + 4) h5x
        have h6x : (x + 6) % 2 = 0 :=
          mod_two_succ_1_0_from (x + 5) h5x
        simp [op_1661_1657,h5y',h4x,h5x,h6x]
    · by_cases h5y: (y + 5) % 2 = 0
      · have h5x : (x + 5) % 2 = 1 := by
          simp_all only [Nat.mod_two_ne_zero]
        have h4x : (x + 4) % 2 = 0 :=
          mod_two_pred_1_0_to (x + 4) h5x
        have h6x : (x + 6) % 2 = 0 :=
          mod_two_succ_1_0_from (x + 5) h5x
        simp [op_1661_1657,h5y,h4x,h5x,h6x]
      · have h5y' : (y + 5) % 2 = 1 :=
          Nat.mod_two_ne_zero.mp h5y
        have h5x : (x + 5) % 2 = 0 := by
          simp_all only [Nat.mod_two_ne_one, one_ne_zero, not_false_eq_true]
        have h4x : (x + 4) % 2 = 1 :=
          mod_two_pred_0_1_to (x + 4) h5x
        have h6x : (x + 6) % 2 = 1 :=
          mod_two_succ_0_1_from (x + 5) h5x
        simp [op_1661_1657,h5y',h4x,h5x,h6x]

  | 0, x+5, y+5 | 1, x+5, y+5 | 2, x+5, y+5 | 3, x+5, y+5 | 4, x+5, y+5 =>
    by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
    · try {rw [op_left_eq x y hxy5]}
      by_cases h5y : (y + 5) % 2 = 0
      · have h5x : (x + 5) % 2 = 0 := by
          rw [hxy5]
          exact h5y
        have h4x : (x + 4) % 2 = 1 :=
          mod_two_pred_0_1_to (x + 4) h5x
        simp [op_1661_1657,h4x,h5x,h5y]
      · have h5y' : (y + 5) % 2 = 1 :=
          Nat.mod_two_ne_zero.mp h5y
        have h5x : (x + 5) % 2 = 1 := by
          rw [hxy5]
          exact h5y'
        have h4x : (x + 4) % 2 = 0 :=
          mod_two_pred_1_0_to (x + 4) h5x
        simp [op_1661_1657,h5x,h5y',h4x]
    · rw [op_left_ne x y hxy5]
      by_cases h5y : (y + 5) % 2 = 0
      · have h5x : (x + 5) % 2 = 1 := by
          simp_all only [Nat.mod_two_ne_zero]
        have h6x : (x + 6) % 2 = 0 :=
          mod_two_succ_1_0_from (x + 5) h5x
        have h7x : (x + 7) % 2 = 1 :=
          mod_two_succ_0_1_from (x + 6) h6x
        simp [op_1661_1657,h5x,h6x,h7x]
      · have h5y' : (y + 5) % 2 = 1 :=
          Nat.mod_two_ne_zero.mp h5y
        have h5x : (x + 5) % 2 = 0 := by
          simp_all only [Nat.mod_two_ne_one, one_ne_zero, not_false_eq_true]
        have h6x : (x + 6) % 2 = 1 :=
          mod_two_succ_0_1_from (x + 5) h5x
        have h7x : (x + 7) % 2 = 0 :=
          mod_two_succ_1_0_from (x + 6) h6x
        simp [op_1661_1657,h5x,h6x,h7x]


@[equational_result]
theorem Equation1661_not_implies_Equation1657 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation1657 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp only [Equation1661, magN, op]
    exact op_1661_1657_satisfies_1661
  · simp only [not_forall]
    exists 0, 1
    simp [magN,op,op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation1860 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation1860 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation1657
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation1657 G' ↔ Equation1860 (Op G') := by aesop
    rwa [h4] at h2

@[equational_result]
theorem Equation1661_not_implies_Equation1630 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation1630 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp only [Equation1661, magN, op]
    exact op_1661_1657_satisfies_1661
  · simp only [not_forall]
    exists 1, 0
    simp [magN,op,op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation1884 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation1884 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation1630
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation1630 G' ↔ Equation1884 (Op G') := by aesop
    rwa [h4] at h2

@[equational_result]
theorem Equation1661_not_implies_Equation1833 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation1833 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp only [Equation1661, magN, op]
    exact op_1661_1657_satisfies_1661
  · simp only [not_forall]
    exists 3, 0
    simp [magN,op,op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation1681 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation1681 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation1833
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation1833 G' ↔ Equation1681 (Op G') := by aesop
    rwa [h4] at h2

@[equational_result]
theorem Equation1661_not_implies_Equation1837 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation1837 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp [Equation1661, magN, op]
    exact op_1661_1657_satisfies_1661
  · simp only [not_forall]
    exists 3, 0
    simp [magN,op,op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation1634 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation1634 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation1837
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation1837 G' ↔ Equation1634 (Op G') := by aesop
    rwa [h4] at h2

@[equational_result]
theorem Equation1661_not_implies_Equation1851 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation1851 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp only [Equation1661, magN, op]
    exact op_1661_1657_satisfies_1661
  · simp only [not_forall]
    exists 0, 3
    simp [magN,op,op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation1721 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation1721 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation1851
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation1851 G' ↔ Equation1721 (Op G') := by aesop
    rwa [h4] at h2

@[equational_result]
theorem Equation1661_not_implies_Equation1860 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation1860 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp [Equation1661, magN, op]
    exact op_1661_1657_satisfies_1661
  simp only [not_forall]
  exists 0, 3
  simp [magN,op,op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation1657 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation1657 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation1860
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation1860 G' ↔ Equation1657 (Op G') := by aesop
    rwa [h4] at h2

@[equational_result]
theorem Equation1661_not_implies_Equation2443 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation2443 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp only [Equation1661,magN, op]
    exact op_1661_1657_satisfies_1661
  · simp only [not_forall]
    exists 1, 0
    simp [magN,op,op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation1035 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation1035 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation2443
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation2443 G' ↔ Equation1035 (Op G') := by aesop
    rwa [h4] at h2

@[equational_result]
theorem Equation1661_not_implies_Equation2467 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation2467 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp only [Equation1661, magN, op]
    exact op_1661_1657_satisfies_1661
  · simp only [not_forall]
    exists 0, 1
    simp [magN,op,op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation1085 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation1085 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation2467
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation2467 G' ↔ Equation1085 (Op G') := by aesop
    rwa [h4] at h2

@[equational_result]
theorem Equation1661_not_implies_Equation3457 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation3457 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp only [Equation1661, magN, op]
    exact op_1661_1657_satisfies_1661
  · simp only [not_forall]
    exists 1, 0
    simp [magN,op,op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation3877 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation3877 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation3457
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation3457 G' ↔ Equation3877 (Op G') := by aesop
    rwa [h4] at h2

@[equational_result]
theorem Equation1661_not_implies_Equation3521 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation3521 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp only [Equation1661, magN, op]
    exact op_1661_1657_satisfies_1661
  · simp only [not_forall]
    exists 0, 1
    simp [magN, op, op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation3952 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation3952 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation3521
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation3521 G' ↔ Equation3952 (Op G') := forall_comm
    rwa [h4] at h2

@[equational_result]
theorem Equation1661_not_implies_Equation4268 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation4268 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp only [Equation1661, magN, op]
    exact op_1661_1657_satisfies_1661
  · simp only [not_forall]
    exists 3, 0
    simp [magN, op, op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation4587 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation4587 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation4268
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation4268 G' ↔ Equation4587 (Op G') := by aesop
    rwa [h4] at h2

@[equational_result]
theorem Equation1661_not_implies_Equation4314 :
  ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation4314 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  refine ⟨ℕ, magN, And.intro ?_ ?_⟩
  · simp only [Equation1661, magN, op]
    exact op_1661_1657_satisfies_1661
  · simp only [not_forall]
    exists 0, 3
    simp [magN,op,op_1661_1657]

/-- Dual of the previous result -/
@[equational_result]
theorem Equation1979_not_implies_Equation4606 : ∃ (G : Type) (_ : Magma G), Equation1979 G ∧ ¬ Equation4606 G := by
  obtain ⟨G', G'Magma, h1, h2⟩ := Equation1661_not_implies_Equation4314
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h3 : Equation1661 G' ↔ Equation1979 (Op G') := by aesop
    rwa [h3] at h1
  · have h4 : Equation4314 G' ↔ Equation4606 (Op G') := by
      unfold Equation4314 Equation4606
      aesop
    rwa [h4] at h2
