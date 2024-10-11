import equational_theories.Equations.All
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import equational_theories.ForMathlib.Algebra.Group.Nat

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

private theorem mod_two_ne_zero_direct (n : ℕ) (h : n % 2 ≠ 0) : n % 2 = 1 := by
  have h_cases : n % 2 = 0 ∨ n % 2 = 1 := by
    have h_mod : n % 2 < 2 := Nat.mod_lt n (Nat.zero_lt_succ 1)
    interval_cases (n % 2)
    simp_all only [ne_eq, not_true_eq_false]
    simp_all only [ne_eq, one_ne_zero, not_false_eq_true, Nat.one_lt_ofNat, or_true]
  cases h_cases with
  | inl h0 => contradiction
  | inr h1 => exact h1

private theorem mod_two_succ_0_1_from (n : ℕ) : n % 2 = 0 → (n + 1) % 2 = 1 := by
  intro nm2
  have nm2' : n % 2 = 0 % 2 := by
    norm_num
    exact nm2
  exact (Nat.add_mod_eq_add_mod_right 1 nm2')

private theorem mod_two_succ_1_0_from (n : ℕ) : n % 2 = 1 → (n + 1) % 2 = 0 := by
  intro nm2
  have nm2' : n % 2 = 1 % 2 := by
    norm_num
    exact nm2
  exact (Nat.add_mod_eq_add_mod_right 1 nm2')

private theorem mod_two_pred_0_1_to (n : ℕ) : (n + 1) % 2 = 0 → n % 2 = 1 := by
  intro nm2
  by_cases that : n % 2 = 0
  · have : (n + 1) % 2 = 1 := mod_two_succ_0_1_from n that
    simp_all only [one_ne_zero]
  · simp_all only [ne_eq, Nat.mod_two_ne_zero, implies_true]

private theorem mod_two_pred_1_0_to (n : ℕ) : (n + 1) % 2 = 1 → n % 2 = 0 := by
  intro nm2
  by_cases that : n % 2 = 0
  · simp_all only [ne_eq, Nat.mod_two_ne_zero, implies_true, one_ne_zero]
  · have : n % 2 = 1 := mod_two_ne_zero_direct n that
    have nm3 : (n + 1) % 2 = 0 := mod_two_succ_1_0_from n this
    simp_all only [zero_ne_one]

private theorem mod_two_ne_down_to (n m : ℕ) : (n + 1) % 2 = m % 2 → ¬ n % 2 = m % 2 := by
  intro hyp assm
  by_cases n0: (n % 2 = 0)
  · have n1 : (n + 1) % 2 = 1 := mod_two_succ_0_1_from n n0
    have bad : 0 = 1 := by simp_all only [Nat.add_mod_mod]
    contradiction
  · have nz1: (n + 1) % 2 = 1 := by
      simp_all only [Nat.mod_two_ne_zero]
    have nz0: n % 2 = 1 := by
      simp_all only [Nat.mod_two_ne_zero, Nat.add_mod_mod]
    have ns0 : (n + 1) % 2 = 0 := mod_two_succ_1_0_from n nz0
    have bad : 0 = 1 := by simp_all only [Nat.add_mod_mod]
    contradiction

private theorem mod_two_eq_down_to (n m : ℕ) : (n + 1) % 2 ≠ m % 2 → n % 2 = m % 2 := by
  intro hyp
  by_cases n0: (n % 2 = 0)
  · have e1 : (n + 1) % 2 = 1 := by
      simp_all only [ne_eq, Nat.mod_two_ne_zero, implies_true]
      exact (mod_two_succ_0_1_from n n0)
    have m2_neq_1 : m % 2 ≠ 1 := by
      intro assm
      simp_all only [ne_eq, Nat.mod_two_ne_zero, implies_true, not_true_eq_false]
    have m2_eq_0 : m % 2 = 0 := by
      simp_all only [ne_eq, Nat.mod_two_ne_zero, implies_true, Nat.mod_two_ne_one]
    simp_all only [ne_eq, Nat.mod_two_ne_zero, implies_true, one_ne_zero, not_false_eq_true, zero_ne_one]

  · have n1 : n % 2 = 1 := by
      simp_all only [ne_eq, Nat.mod_two_ne_zero, implies_true]
    have n11 : (n + 1) % 2 = 0 := mod_two_succ_1_0_from n n1
    have m2_neq_0 : m % 2 ≠ 0 := by
      intro assm
      simp_all only [ne_eq, Nat.mod_two_ne_zero, implies_true, not_true_eq_false]
    simp_all only [ne_eq, Nat.mod_two_ne_zero, implies_true, one_ne_zero, not_false_eq_true]

private theorem mod_two_ne_up_from (n m : ℕ) : n % 2 = m % 2 → ¬ (n + 1) % 2 = m % 2 := by
  intro hyp assm
  by_cases n0: (n % 2 = 0)
  · have n1 : (n + 1) % 2 = 1 := mod_two_succ_0_1_from n n0
    have bad : 0 = 1 := by simp_all only [Nat.add_mod_mod]
    contradiction
  · have nz1: (n + 1) % 2 = 1 := by
      simp_all only [Nat.mod_two_ne_zero]
    have nz0: n % 2 = 1 := by
      simp_all only [Nat.mod_two_ne_zero, Nat.add_mod_mod]
    have ns0 : (n + 1) % 2 = 0 := mod_two_succ_1_0_from n nz0
    have bad : 0 = 1 := by simp_all only [Nat.add_mod_mod]
    contradiction

private theorem mod_two_eq_up_from (n m : ℕ) : n % 2 ≠ m % 2 → (n + 1) % 2 = m % 2 := by
  intro hyp
  by_cases n0: (n % 2 = 0)
  · have e1 : (n + 1) % 2 = 1 := by
      simp_all only [ne_eq, Nat.mod_two_ne_zero, implies_true]
      exact (mod_two_succ_0_1_from n n0)
    have m2_eq_1 : m % 2 = 1 := by
      have : m % 2 ≠ 0 := by
        rw [← n0]
        exact (Ne.symm hyp)
      exact (mod_two_ne_zero_direct m this)
    simp_all only [ne_eq, zero_ne_one, not_false_eq_true]
  · have n1 : n % 2 = 1 := by
      simp_all only [ne_eq, Nat.mod_two_ne_zero, implies_true]
    have n11 : (n + 1) % 2 = 0 := mod_two_succ_1_0_from n n1
    have m2_eq_0 : m % 2 = 0 := by
      have : m %2 ≠ 1 := by
        rw [← n1]
        exact (Ne.symm hyp)
      simp_all only [ne_eq, one_ne_zero, not_false_eq_true, Nat.mod_two_ne_one]
    simp_all only [ne_eq, one_ne_zero, not_false_eq_true]


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
    have y4o : (y + 4) % 2 = 1 := mod_two_pred_0_1_to (y + 4) y5e
    have y6o : (y + 6) % 2 = 1 := mod_two_succ_0_1_from (y + 5) y5e
    match x with
    | 0 | 1 | 2 | 3 | 4 =>
      simp [op_1661_1657,y5e,y4o,y6o,delta_right_even]
    | n+5 =>
      by_cases n5eo : (n + 5) % 2 = 0
      · simp [op_1661_1657,y5e,n5eo,y4o,delta_right_even]
      · have n5o : (n + 5) % 2 = 1 := mod_two_ne_zero_direct (n + 5) n5eo
        simp [op_1661_1657,y5e,y6o,n5o,delta_right_even]

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
    have y4e : (y + 4) % 2 = 0 := mod_two_pred_1_0_to (y + 4) y5o'
    have y6e : (y + 6) % 2 = 0 := mod_two_succ_1_0_from (y + 5) y5o'
    match x with
    | 0 | 1 | 2 | 3 | 4 =>
      simp [op_1661_1657,y5o',y4e,y6e,delta_right_odd]
    | n+5 =>
      by_cases n5eo : (n + 5) % 2 = 0
      · simp [op_1661_1657,y5o',n5eo,y4e,y6e,delta_right_odd]
      · have n5o : (n + 5) % 2 = 1 := mod_two_ne_zero_direct (n + 5) n5eo
        simp [op_1661_1657,y5o',n5o,y4e,delta_right_odd]

private theorem op_left_eq (x y : ℕ) : (x + 5) % 2 = (y + 5) % 2 → op_1661_1657 (x + 5) (y + 5) = x + 4 := by
  simp [op_1661_1657]

private theorem op_left_ne (x y : ℕ) : ¬ ((x + 5) % 2 = (y + 5) % 2) → op_1661_1657 (x + 5) (y + 5) = x + 6 := by
  simp [op_1661_1657]

private theorem op_right_eq (y z : ℕ) : (y + 5) % 2 = (z + 5) % 2 → op_1661_1657 (op_1661_1657 (y + 5) (z + 5)) (y + 5) = y + 5 := by
  intro yz5
  have yz45 : ¬(y + 4) % 2 = (z + 5) % 2 := mod_two_ne_down_to (y + 4) (z + 5) yz5
  simp [op_1661_1657,yz5, yz45]

private theorem op_right_ne (y z : ℕ) : ¬ (y + 5) % 2 = (z + 5) % 2 → op_1661_1657 (op_1661_1657 (y + 5) (z + 5)) (y + 5) = y + 7 := by
  intro yz5
  simp [op_1661_1657,yz5]
  have r : (y + 5) % 2 = (y + 5) % 2 := by simp
  exact (mod_two_ne_up_from (y + 5) (y + 5) r)


/-
  Now we're ready to prove that 1661 does not imply 1657. This has to be done by
  a case analysis both on the patched cases and the rest of the numbers modulo 2.
  Most of this is routine w/ the lemmata proven above. The cases that require some
  care are the ones that involve two non-exceptional numbers and one exceptional
  number. These are handled at the end.

  Keep in mind that the exceptional numbers are 0,1,2,3,4, not just the 0,1,2,3
  that we match on.
-/

@[equational_result]
theorem Equation1661_not_implies_Equation1657 : ∃ (G : Type) (_ : Magma G), Equation1661 G ∧ ¬ Equation1657 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1661_1657 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  apply And.intro
  simp [Equation1661]

  have op_property : ∀ x y z : ℕ, x = op (op x y) (op (op y z) y) := by
    intro xo yo zo
    simp [op]
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
      simp [op,op_1661_1657]

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
      simp [op,op_1661_1657]
      by_cases hx5 : (x + 5) % 2 = 0
      · have hx4 : (x + 4) % 2 = 1 :=
          mod_two_pred_0_1_to (x + 4) hx5
        have hx6 : (x + 6) % 2 = 1 :=
          mod_two_succ_0_1_from (x + 5) hx5
        have hx7 : (x + 7) % 2 = 0 :=
          mod_two_succ_1_0_from (x + 6) hx6
        simp [hx4, hx5, hx6, hx7]
      · have hx5' : (x + 5) % 2 = 1 :=
          mod_two_ne_zero_direct (x + 5) hx5
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
          simp [op,op_1661_1657,hxy4]
        · rw [op_left_ne x y hxy5]
          have hxy6 : (x + 6) % 2 = (y + 5) % 2 :=
            mod_two_eq_up_from (x + 5) (y + 5) hxy5
          simp [op,op_1661_1657,hxy6]
      · rw [op_right_ne y z hyz5]
        by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
        · rw [op_left_eq x y hxy5]
          have hxy45 : (x + 4) % 2 ≠ (y + 5) % 2 :=
            mod_two_ne_down_to (x + 4) (y + 5) hxy5
          have hxy46 : (y + 6) % 2 = (x + 4) % 2 :=
            mod_two_eq_up_from (y + 5) (x + 4) (Ne.symm hxy45)
          have hxy43 : ¬ (x + 4) % 2 = (y + 7) % 2 :=
            Ne.symm (mod_two_ne_up_from (y + 6) (x + 4) hxy46)
          simp [op,op_1661_1657,hxy43]
        · rw [op_left_ne x y hxy5]
          simp [op,op_1661_1657]
          have hxy56 : (x + 6) % 2 = (y + 5) % 2 :=
            mod_two_eq_up_from (x + 5) (y + 5) hxy5
          have hxy6 : (y + 6) % 2 ≠ (x + 6) % 2 :=
            mod_two_ne_up_from (y + 5) (x + 6) (Eq.symm hxy56)
          have hxy67 : (x + 6) % 2 = (y + 7) % 2 :=
            Eq.symm (mod_two_eq_up_from (y + 6) (x + 6) hxy6)
          simp [op,op_1661_1657,hxy67]

    | x+5, y+5, 0 =>  -- also 2,4
      by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
      · rw [op_left_eq x y hxy5]
        by_cases h5 : (y + 5) % 2 = 0
        · rw [op_right_even y h5 0]
          simp only [delta_right_even]
          have hxy45 : ¬ (x + 4) % 2 = (y + 5) % 2 :=
            mod_two_ne_down_to (x + 4) (y + 5) hxy5
          simp [op,op_1661_1657,hxy45]
        · rw [op_right_odd y h5 0]
          simp only [delta_right_odd]
          have hxy56 : (y + 6) % 2 ≠ (x + 5) % 2 :=
            mod_two_ne_up_from (y + 5) (x + 5) (Eq.symm hxy5)
          have hxy57 : (x + 5) % 2 = (y + 7) % 2 :=
            Eq.symm (mod_two_eq_up_from (y + 6) (x + 5) hxy56)
          have hxy47 : ¬ (x + 4) % 2 = (y + 7) % 2 :=
            mod_two_ne_down_to (x + 4) (y +7) hxy57
          simp [op,op_1661_1657,hxy47]
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
          have hxy56 : (y + 6) % 2 = (x + 5) % 2 :=
            mod_two_eq_up_from (y + 5) (x + 5) (Ne.symm hxy5)
          have hxy57 : (y + 7) % 2 ≠ (x + 5) % 2 :=
            mod_two_ne_up_from (y + 6) (x + 5) hxy56
          have hxy67 : (x + 6) % 2 = (y + 7) % 2 :=
            mod_two_eq_up_from (x + 5) (y + 7) (Ne.symm hxy57)
          simp [op,op_1661_1657,hxy67]

    | x+5, y+5, 2 =>  -- also 0,4
      by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
      · rw [op_left_eq x y hxy5]
        by_cases h5 : (y + 5) % 2 = 0
        · rw [op_right_even y h5 2]
          simp only [delta_right_even]
          have hxy45 : ¬ (x + 4) % 2 = (y + 5) % 2 :=
            mod_two_ne_down_to (x + 4) (y + 5) hxy5
          simp [op,op_1661_1657,hxy45]
        · rw [op_right_odd y h5 2]
          simp only [delta_right_odd]
          have hxy56 : (y + 6) % 2 ≠ (x + 5) % 2 :=
            mod_two_ne_up_from (y + 5) (x + 5) (Eq.symm hxy5)
          have hxy57 : (x + 5) % 2 = (y + 7) % 2 :=
            Eq.symm (mod_two_eq_up_from (y + 6) (x + 5) hxy56)
          have hxy47 : ¬ (x + 4) % 2 = (y + 7) % 2 :=
            mod_two_ne_down_to (x + 4) (y +7) hxy57
          simp [op,op_1661_1657,hxy47]
      · rw [op_left_ne x y hxy5]
        by_cases h5 : (y + 5) % 2 = 0
        · rw [op_right_even y h5 2]
          simp only [delta_right_even]
          have hxy65 : (x + 6) % 2 = (y + 5) % 2 :=
            mod_two_eq_up_from (x + 5) (y + 5) hxy5
          rw [op_left_eq (x+1) y]
          exact hxy65
        · rw [op_right_odd y h5 2]
          simp only [delta_right_odd]
          have hxy56 : (y + 6) % 2 = (x + 5) % 2 :=
            mod_two_eq_up_from (y + 5) (x + 5) (Ne.symm hxy5)
          have hxy57 : (y + 7) % 2 ≠ (x + 5) % 2 :=
            mod_two_ne_up_from (y + 6) (x + 5) hxy56
          have hxy67 : (x + 6) % 2 = (y + 7) % 2 :=
            mod_two_eq_up_from (x + 5) (y + 7) (Ne.symm hxy57)
          simp [op,op_1661_1657,hxy67]

    | x+5, y+5, 4 =>  -- also 0,2
      by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
      · rw [op_left_eq x y hxy5]
        by_cases h5 : (y + 5) % 2 = 0
        · rw [op_right_even y h5 4]
          simp only [delta_right_even]
          have hxy45 : ¬ (x + 4) % 2 = (y + 5) % 2 :=
            mod_two_ne_down_to (x + 4) (y + 5) hxy5
          simp [op,op_1661_1657,hxy45]
        · rw [op_right_odd y h5 4]
          simp only [delta_right_odd]
          have hxy56 : (y + 6) % 2 ≠ (x + 5) % 2 :=
            mod_two_ne_up_from (y + 5) (x + 5) (Eq.symm hxy5)
          have hxy57 : (x + 5) % 2 = (y + 7) % 2 :=
            Eq.symm (mod_two_eq_up_from (y + 6) (x + 5) hxy56)
          have hxy47 : ¬ (x + 4) % 2 = (y + 7) % 2 :=
            mod_two_ne_down_to (x + 4) (y +7) hxy57
          simp [op,op_1661_1657,hxy47]
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
          have hxy56 : (y + 6) % 2 = (x + 5) % 2 :=
            mod_two_eq_up_from (y + 5) (x + 5) (Ne.symm hxy5)
          have hxy57 : (y + 7) % 2 ≠ (x + 5) % 2 :=
            mod_two_ne_up_from (y + 6) (x + 5) hxy56
          have hxy67 : (x + 6) % 2 = (y + 7) % 2 :=
            mod_two_eq_up_from (x + 5) (y + 7) (Ne.symm hxy57)
          simp [op,op_1661_1657,hxy67]

    | x+5, y+5, 1 =>  -- also 3
      by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
      · rw [op_left_eq x y hxy5]
        by_cases h5 : (y + 5) % 2 = 0
        · rw [op_right_even y h5 1]
          simp only [delta_right_even]
          have hxy56 : (y + 6) % 2 ≠ (x + 5) % 2 :=
            mod_two_ne_up_from (y + 5) (x + 5) (Eq.symm hxy5)
          have hxy57 : (x + 5) % 2 = (y + 7) % 2 :=
            Eq.symm (mod_two_eq_up_from (y + 6) (x + 5) hxy56)
          have hxy47 : ¬ (x + 4) % 2 = (y + 7) % 2 :=
            mod_two_ne_down_to (x + 4) (y +7) hxy57
          simp [op,op_1661_1657,hxy47]
        · rw [op_right_odd y h5 1]
          simp only [delta_right_odd]
          have hxy45 : (x + 4) % 2 ≠ (y + 5) % 2 :=
            mod_two_ne_down_to (x + 4) (y + 5) hxy5
          simp [op,op_1661_1657,hxy5,hxy45]
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
          simp [op,op_1661_1657,hxy56]

    | x+5, y+5, 3 =>  -- also 1
      by_cases hxy5 : (x + 5) % 2 = (y + 5) % 2
      · rw [op_left_eq x y hxy5]
        by_cases h5 : (y + 5) % 2 = 0
        · rw [op_right_even y h5 3]
          simp only [delta_right_even]
          have hxy56 : (y + 6) % 2 ≠ (x + 5) % 2 :=
            mod_two_ne_up_from (y + 5) (x + 5) (Eq.symm hxy5)
          have hxy57 : (x + 5) % 2 = (y + 7) % 2 :=
            Eq.symm (mod_two_eq_up_from (y + 6) (x + 5) hxy56)
          have hxy47 : ¬ (x + 4) % 2 = (y + 7) % 2 :=
            mod_two_ne_down_to (x + 4) (y +7) hxy57
          simp [op,op_1661_1657,hxy47]
        · rw [op_right_odd y h5 3]
          simp only [delta_right_odd]
          have hxy45 : (x + 4) % 2 ≠ (y + 5) % 2 :=
            mod_two_ne_down_to (x + 4) (y + 5) hxy5
          simp [op,op_1661_1657,hxy5,hxy45]
      · rw [op_left_ne x y hxy5]
        by_cases h5 : (y + 5) % 2 = 0
        · rw [op_right_even y h5 3]
          simp only [delta_right_even]
          have hxy56 : (y + 6) % 2 = (x + 5) % 2 :=
            mod_two_eq_up_from (y + 5) (x + 5) (Ne.symm hxy5)
          have hxy57 : (y + 7) % 2 ≠ (x + 5) % 2 :=
            mod_two_ne_up_from (y + 6) (x + 5) hxy56
          have hxy67 : (x + 6) % 2 = (y + 7) % 2 :=
            mod_two_eq_up_from (x + 5) (y + 7) (Ne.symm hxy57)
          rw [op_left_eq (x+1) (y+2) hxy67]
        · rw [op_right_odd y h5 3]
          simp only [delta_right_odd]
          have hxy56 : (x + 6) % 2 = (y + 5) % 2 :=
            mod_two_eq_up_from (x + 5) (y + 5) hxy5
          simp [op,op_1661_1657,hxy56]

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
          simp [op,op_1661_1657,h5y]
          simp [h4x,h5x,h6x]
        · have h5y' : (y + 5) % 2 = 1 :=
            mod_two_ne_zero_direct (y + 5) h5y
          have h5x : (x + 5) % 2 = 1 := by
            rw [hxy5]
            exact h5y'
          have h4x : (x + 4) % 2 = 0 :=
            mod_two_pred_1_0_to (x + 4) h5x
          have h6x : (x + 6) % 2 = 0 :=
            mod_two_succ_1_0_from (x + 5) h5x
          simp [op,op_1661_1657,h5y',h4x,h5x,h6x]
      · by_cases h5y: (y + 5) % 2 = 0
        · have h5x : (x + 5) % 2 = 1 := by
            simp_all only [Nat.mod_two_ne_zero]
          have h4x : (x + 4) % 2 = 0 :=
            mod_two_pred_1_0_to (x + 4) h5x
          have h6x : (x + 6) % 2 = 0 :=
            mod_two_succ_1_0_from (x + 5) h5x
          simp [op,op_1661_1657,h5y,h4x,h5x,h6x]
        · have h5y' : (y + 5) % 2 = 1 :=
            mod_two_ne_zero_direct (y + 5) h5y
          have h5x : (x + 5) % 2 = 0 := by
            simp_all only [Nat.mod_two_ne_one, one_ne_zero, not_false_eq_true]
          have h4x : (x + 4) % 2 = 1 :=
            mod_two_pred_0_1_to (x + 4) h5x
          have h6x : (x + 6) % 2 = 1 :=
            mod_two_succ_0_1_from (x + 5) h5x
          simp [op,op_1661_1657,h5y',h4x,h5x,h6x]

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
            mod_two_ne_zero_direct (y + 5) h5y
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
            mod_two_ne_zero_direct (y + 5) h5y
          have h5x : (x + 5) % 2 = 0 := by
            simp_all only [Nat.mod_two_ne_one, one_ne_zero, not_false_eq_true]
          have h6x : (x + 6) % 2 = 1 :=
            mod_two_succ_0_1_from (x + 5) h5x
          have h7x : (x + 7) % 2 = 0 :=
            mod_two_succ_1_0_from (x + 6) h6x
          simp [op_1661_1657,h5x,h6x,h7x]
  simp [magN,op]
  exact op_property
  simp
  exists 0, 1
  simp [magN,op,op_1661_1657]
