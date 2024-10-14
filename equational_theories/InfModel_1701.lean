import equational_theories.Equations.All
import equational_theories.MagmaOp
import Aesop
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import equational_theories.Mathlib.Algebra.Group.Nat

/-
  The proof follows the general strategy set out in InfModel_1701. We start from
  a simple infinite model of 1701, then patch it to break consequents. The bulk is
  showing that the patch construction retains 1701, the counterexamples part is
  immediate. Since this has to be done by a case analysis both on the patched
  cases and the rest of the numbers modulo 2, we use the following mod_two
  lemmata.
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
  The model we start with is the transpose of the original model for 1661.
  Showing that 1701 does not imply 8 is exceedingly simple: we need only truncate,
  not patch further. However, 3253 and 4587 cannot be refuted this way: those have
  to be dealt with in two separate constructions.
-/

private def op_1701_8 (x : ℕ) (y : ℕ) : ℕ :=
  match y with
  | 0 => 0
  | n + 1 =>
    if x % 2 = y % 2
    then n else n + 2

/-
  This proof is much nicer than the others in InfModel_1661 and below, since simp here
  does not time out with (deterministic) timeout at `isDefEq`.
  TODO: Write a macro which simplifies this kind of argument.
-/

private theorem op_1701_8_satisfies_1701 :
  ∀ (x y z : ℕ), x = op_1701_8 (op_1701_8 y x) (op_1701_8 (op_1701_8 z x) x) := by
  intro xo yo zo
  match xo,yo,zo with
  | x+1, y+1, z+1 =>
    by_cases sx_cong_sz : ((x + 1) % 2 = (z + 1) % 2)
    · by_cases sx_cong_0 : ((x + 1) % 2 = 0)
      · have sz_cong_0 : ((z + 1) % 2 = 0) := by omega
        have x_cong_1 : (x % 2 = 1) := mod_two_pred_0_1_to x sx_cong_0
        have ssx_cong_1 : ((x + 2) % 2 = 1) := mod_two_succ_0_1_from (x+1) sx_cong_0
        by_cases sy_cong_0 : ((y + 1) % 2 = 0)
        · simp [op_1701_8,sx_cong_sz,x_cong_1,sz_cong_0,ssx_cong_1,sy_cong_0]
        · have sy_cong_1 : ((y + 1) % 2 = 1) := Nat.mod_two_ne_zero.mp sy_cong_0
          simp [op_1701_8,sx_cong_sz,x_cong_1,sz_cong_0,ssx_cong_1,sy_cong_1]
      · have sx_cong_1 : (x + 1) % 2 = 1 := by omega
        have sz_cong_1 : (z + 1) % 2 = 1 := by omega
        by_cases sy_cong_0 : ((y + 1) % 2 = 0)
        · simp [op_1701_8,sx_cong_sz,sy_cong_0,sz_cong_1
               ,Nat.mod_two_ne_zero,mod_two_ne_down_to
               ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
               ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
               ]
        · have sy_cong_1 : (y + 1) % 2 = 1 := by omega
          simp [op_1701_8,sx_cong_sz,sy_cong_1,sz_cong_1
               ,Nat.mod_two_ne_zero,mod_two_ne_down_to
               ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
               ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
               ]

    · by_cases sx_cong_0 : ((x + 1) % 2 = 0)
      · have sz_cong_1 : ((z + 1) % 2 = 1) := by omega
        by_cases sy_cong_0 : ((y + 1) % 2 = 0)
        · simp [op_1701_8,sx_cong_sz,sx_cong_0,sy_cong_0,sz_cong_1
               ,Nat.mod_two_ne_zero,mod_two_ne_down_to
               ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
               ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
               ]
        · have sy_cong_1 : ((y + 1) % 2 = 1) := Nat.mod_two_ne_zero.mp sy_cong_0
          simp [op_1701_8,sx_cong_sz,sx_cong_0,sy_cong_1,sz_cong_1
               ,Nat.mod_two_ne_zero,mod_two_ne_down_to
               ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
               ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
               ]
      · have sx_cong_1 : (x + 1) % 2 = 1 := by omega
        have sz_cong_0 : (z + 1) % 2 = 0 := by omega
        by_cases sy_cong_0 : ((y + 1) % 2 = 0)
        · simp [op_1701_8,sx_cong_sz,sx_cong_1,sy_cong_0,sz_cong_0
               ,Nat.mod_two_ne_zero,mod_two_ne_down_to
               ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
               ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
               ]
        · have sy_cong_1 : (y + 1) % 2 = 1 := by omega
          simp [op_1701_8,sx_cong_sz,sx_cong_1,sy_cong_1,sz_cong_0
               ,Nat.mod_two_ne_zero,mod_two_ne_down_to
               ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
               ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
               ]
  | x+1, y+1, 0 | x+1, 0, y+1 | 0, _+1, _+1 =>
    simp [op_1701_8]
    try{
      by_cases sx_cong_0 : (x + 1) % 2 = 0
      · by_cases sy_cong_0 : (y + 1) % 2 = 0
        · simp [sx_cong_0,sy_cong_0
              ,Nat.mod_two_ne_zero,mod_two_ne_down_to
              ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
              ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
              ]
        · simp [sx_cong_0,sy_cong_0
              ,Nat.mod_two_ne_zero,mod_two_ne_down_to
              ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
              ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
              ]
      · have sx_cong_1 : (x + 1) % 2 = 1 := by omega
        by_cases sy_cong_0 : (y + 1) % 2 = 0
        · simp [sx_cong_1,sy_cong_0
              ,Nat.mod_two_ne_zero,mod_two_ne_down_to
              ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
              ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
              ]
        · have sy_cong_1 : (y + 1) % 2 = 1 := by omega
          simp [sx_cong_1,sy_cong_1
              ,Nat.mod_two_ne_zero,mod_two_ne_down_to
              ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
              ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
              ]
    }
   | x+1, 0, 0 | 0, _+1, 0 | 0, 0, _+1 =>
      simp [op_1701_8]
      try {
        by_cases sx_cong_0 : (x + 1) % 2 = 0
        · simp [sx_cong_0
              ,Nat.mod_two_ne_zero,mod_two_ne_down_to
              ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
              ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
              ]
        · have sx_cong_1 : (x + 1) % 2 = 1 := by omega
          simp [sx_cong_1
              ,Nat.mod_two_ne_zero,mod_two_ne_down_to
              ,mod_two_succ_0_1_from,mod_two_succ_1_0_from
              ,mod_two_pred_0_1_to,mod_two_pred_1_0_to
              ]
      }
   | 0, 0, 0 => simp [op_1701_8]


@[equational_result]
theorem Equation1701_not_implies_Equation8 :
  ∃ (G : Type) (_ : Magma G), Equation1701 G ∧ ¬ Equation8 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1701_8 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation1701,magN,op]
  apply And.intro
  · exact op_1701_8_satisfies_1701
  exists 1


@[equational_result]
theorem Equation1701_not_implies_Equation411 :
  ∃ (G : Type) (_ : Magma G), Equation1701 G ∧ ¬ Equation411 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1701_8 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation1701,magN,op]
  apply And.intro
  · exact op_1701_8_satisfies_1701
  exists 1

@[equational_result]
theorem Equation1701_not_implies_Equation1020 :
  ∃ (G : Type) (_ : Magma G), Equation1701 G ∧ ¬ Equation1020 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1701_8 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation1701,magN,op]
  apply And.intro
  · exact op_1701_8_satisfies_1701
  exists 1

@[equational_result]
theorem Equation1701_not_implies_Equation1035 :
  ∃ (G : Type) (_ : Magma G), Equation1701 G ∧ ¬ Equation1035 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1701_8 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation1701,magN,op]
  apply And.intro
  · exact op_1701_8_satisfies_1701
  exists 1, 1


@[equational_result]
theorem Equation1701_not_implies_Equation1832 :
  ∃ (G : Type) (_ : Magma G), Equation1701 G ∧ ¬ Equation1832 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1701_8 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation1701,magN,op]
  apply And.intro
  · exact op_1701_8_satisfies_1701
  exists 1

@[equational_result]
theorem Equation1701_not_implies_Equation3319 :
  ∃ (G : Type) (_ : Magma G), Equation1701 G ∧ ¬ Equation3319 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1701_8 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation1701,magN,op]
  apply And.intro
  · exact op_1701_8_satisfies_1701
  exists 0, 1

@[equational_result]
theorem Equation1701_not_implies_Equation3862 :
  ∃ (G : Type) (_ : Magma G), Equation1701 G ∧ ¬ Equation3862 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1701_8 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation1701,magN,op]
  apply And.intro
  · exact op_1701_8_satisfies_1701
  exists 1

@[equational_result]
theorem Equation1701_not_implies_Equation1884 :
  ∃ (G : Type) (_ : Magma G), Equation1701 G ∧ ¬ Equation1884 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1701_8 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp [Equation1701,magN,op]
  apply And.intro
  · exact op_1701_8_satisfies_1701
  exists 1, 1


/-
  We can refute 3862 using the small patch below with the same base model.
-/

private def op_1701_3253 (x : ℕ) (y : ℕ) : ℕ :=
  match x, y with
  | 0, 1 | 1, 1 => 1
  | _, 0 | _, 1 => 0
  | _, y+2 =>
    if x % 2 = (y+2) % 2
    then y + 1 else y + 3

private theorem op_1701_3253_satisfies_1701 :
  ∀ (x y z : ℕ), x = op_1701_3253 (op_1701_3253 y x) (op_1701_3253 (op_1701_3253 z x) x) := by
    intro xo yo zo
    match xo with
    | 0     => simp [op_1701_3253]
    | 1     =>
      match yo,zo with
      | 0, 0 | 0, 1 | 0, z+2
      | 1, 0 | 1, 1 | 1, z+2
      | y+2, 0 | y+2, 1 | y+2, z+2 => simp [op_1701_3253]
    | (x+2) =>
      match yo with
      | 0 =>
        by_cases x_cong_0 : x % 2 = 0
        · have x1_cong_1 : (x+1) % 2 = 1 := mod_two_succ_0_1_from _ x_cong_0
          have x2_cong_0 : (x+2) % 2 = 0 := mod_two_succ_1_0_from _ x1_cong_1
          have x3_cong_1 : (x+3) % 2 = 1 := mod_two_succ_0_1_from _ x2_cong_0
          simp [op_1701_3253,x_cong_0]
          by_cases zo_cong_0 : zo % 2 = 0
          · simp [x_cong_0,x1_cong_1,zo_cong_0]
          · have zo_cong_1 : zo % 2 = 1 := Nat.mod_two_ne_zero.mp zo_cong_0
            simp [x_cong_0,x3_cong_1,zo_cong_1]
        · have x_cong_1 : x % 2 = 1 := Nat.mod_two_ne_zero.mp x_cong_0
          have x1_cong_0 : (x+1) % 2 = 0 := mod_two_succ_1_0_from _ x_cong_1
          have x2_cong_1 : (x+2) % 2 = 1 := mod_two_succ_0_1_from _ x1_cong_0
          have x3_cong_0 : (x+3) % 2 = 0 := mod_two_succ_1_0_from _ x2_cong_1
          simp [op_1701_3253,x_cong_1]
          by_cases zo_cong_0 : zo % 2 = 0
          · simp [x_cong_1,zo_cong_0,x1_cong_0,x3_cong_0]
          · have zo_cong_1 : zo % 2 = 1 := Nat.mod_two_ne_zero.mp zo_cong_0
            simp [x_cong_0,x1_cong_0,x3_cong_0,zo_cong_1]
      | 1 =>
        by_cases x_cong_0 : x % 2 = 0
        · have x1_cong_1 : (x+1) % 2 = 1 := mod_two_succ_0_1_from _ x_cong_0
          have x2_cong_0 : (x+2) % 2 = 0 := mod_two_succ_1_0_from _ x1_cong_1
          have x3_cong_1 : (x+3) % 2 = 1 := mod_two_succ_0_1_from _ x2_cong_0
          simp [op_1701_3253,x_cong_0]
          by_cases zo_cong_0 : zo % 2 = 0
          · simp [x_cong_0,x1_cong_1,x3_cong_1,zo_cong_0]
          · have zo_cong_1 : zo % 2 = 1 := Nat.mod_two_ne_zero.mp zo_cong_0
            simp [x_cong_0,x1_cong_1,x3_cong_1,zo_cong_1]
        · have x_cong_1 : x % 2 = 1 := Nat.mod_two_ne_zero.mp x_cong_0
          have x1_cong_0 : (x+1) % 2 = 0 := mod_two_succ_1_0_from _ x_cong_1
          have x2_cong_1 : (x+2) % 2 = 1 := mod_two_succ_0_1_from _ x1_cong_0
          have x3_cong_0 : (x+3) % 2 = 0 := mod_two_succ_1_0_from _ x2_cong_1
          simp [op_1701_3253,x_cong_1]
          by_cases zo_cong_0 : zo % 2 = 0
          · simp [x_cong_1,zo_cong_0,x1_cong_0,x3_cong_0]
          · have zo_cong_1 : zo % 2 = 1 := Nat.mod_two_ne_zero.mp zo_cong_0
            simp [x_cong_0,x1_cong_0,x3_cong_0,zo_cong_1]
      | y+2 =>
        by_cases x_cong_0 : x % 2 = 0
        · have x1_cong_1 : (x+1) % 2 = 1 := mod_two_succ_0_1_from _ x_cong_0
          have x2_cong_0 : (x+2) % 2 = 0 := mod_two_succ_1_0_from _ x1_cong_1
          have x3_cong_1 : (x+3) % 2 = 1 := mod_two_succ_0_1_from _ x2_cong_0
          simp [op_1701_3253,x_cong_0]
          by_cases y_cong_0 : y % 2 = 0
          · simp [y_cong_0,x1_cong_1]
            by_cases zo_cong_0 : zo % 2 = 0
            · simp [x_cong_0,x1_cong_1,x3_cong_1,zo_cong_0]
            · have zo_cong_1 : zo % 2 = 1 := Nat.mod_two_ne_zero.mp zo_cong_0
              simp [x_cong_0,x1_cong_1,x3_cong_1,zo_cong_1]
          · have y_cong_1 : y % 2 = 1 := Nat.mod_two_ne_zero.mp y_cong_0
            simp [y_cong_1,x3_cong_1]
            by_cases zo_cong_0 : zo % 2 = 0
            · simp [x_cong_0,x1_cong_1,x3_cong_1,zo_cong_0]
            · have zo_cong_1 : zo % 2 = 1 := Nat.mod_two_ne_zero.mp zo_cong_0
              simp [x_cong_0,x1_cong_1,x3_cong_1,zo_cong_1]
        · have x_cong_1 : x % 2 = 1 := Nat.mod_two_ne_zero.mp x_cong_0
          have x1_cong_0 : (x+1) % 2 = 0 := mod_two_succ_1_0_from x x_cong_1
          have x2_cong_1 : (x+2) % 2 = 1 := mod_two_succ_0_1_from _ x1_cong_0
          have x3_cong_0 : (x+3) % 2 = 0 := mod_two_succ_1_0_from _ x2_cong_1
          simp [op_1701_3253,x_cong_1]
          by_cases y_cong_0 : y % 2 = 0
          · simp [y_cong_0,x1_cong_0]
            by_cases zo_cong_0 : zo % 2 = 0
            · simp [x_cong_1,x1_cong_0,x3_cong_0,zo_cong_0]
            · have zo_cong_1 : zo % 2 = 1 := Nat.mod_two_ne_zero.mp zo_cong_0
              simp [x_cong_1,x1_cong_0,x3_cong_0,zo_cong_1]
          · have y_cong_1 : y % 2 = 1 := Nat.mod_two_ne_zero.mp y_cong_0
            simp [y_cong_1,x3_cong_0]
            by_cases zo_cong_0 : zo % 2 = 0
            · simp [x_cong_1,x1_cong_0,x3_cong_0,zo_cong_0]
            · have zo_cong_1 : zo % 2 = 1 := Nat.mod_two_ne_zero.mp zo_cong_0
              simp [x_cong_1,x1_cong_0,x3_cong_0,zo_cong_1]


@[equational_result]
theorem Equation1701_not_implies_Equation3252 :
  ∃ (G : Type) (_ : Magma G), Equation1701 G ∧ ¬ Equation3253 G := by
  let op (x : ℕ) (y : ℕ) : ℕ := op_1701_3253 x y
  let magN : Magma ℕ := ⟨fun x y ↦ op x y⟩
  use ℕ, magN
  simp only [Equation3253, not_forall, magN, op]
  exact And.intro op_1701_3253_satisfies_1701 (by exists 2)

/-
  Refuting 4587 requires an extraordinarily complicated patch on the
  same base model.

  Lean seems to struggle a lot with these case distinctions unless we increase
  maxHeartbeats. I already tried to use the strategy of InfModel_1661 where I
  proved a bunch of lemmata first, reminiscent of the original pen-and-paper
  sketch of the argument. But that failed here: at some point, Lean gave up
  on rewrites too, not just simp.

  There's surely a better way to do proofs like these, maybe with macros or
  custom tactics. If you know a solution, feel free to try.
-/

private def op_1701_4587 (x : ℕ) (y : ℕ) : ℕ :=
  match x, y with
  |   0,   2 => 3
  |   0,   3 => 2
  |   1,   0 => 2
  |   1,   1 => 0
  |   2,   3 => 4
  |   3,   2 => 3
  |   _,   0 => 1
  |   _,   1 => 0
  |   _,   2 => 0
  |   x, y+1 =>
    if x % 2 = (y+1) % 2
    then y else y + 2

set_option maxHeartbeats 600000 in
private theorem op_1701_4587_satisfies_1701 :
  ∀ (x y z : ℕ), x = op_1701_4587 (op_1701_4587 y x) (op_1701_4587 (op_1701_4587 z x) x) := by
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
      simp [op_1701_4587]

    | x+5, y+5, z+5 =>
        by_cases x5_cong_0 : ((x + 5) % 2 = 0)
        · have x4_cong_1 : (x + 4) % 2 = 1 := mod_two_pred_0_1_to _ x5_cong_0
          have x6_cong_1 : (x + 6) % 2 = 1 := mod_two_succ_0_1_from _ x5_cong_0
          by_cases y5_cong_0 : ((y + 5) % 2 = 0)
          · by_cases z5_cong_0 : ((z + 5) % 2 = 0)
            · simp [op_1701_4587, x5_cong_0, y5_cong_0, z5_cong_0, x4_cong_1, x6_cong_1]
            · have z5_cong_1 : (z + 5) % 2 = 1 := Nat.mod_two_ne_zero.mp z5_cong_0
              simp [op_1701_4587, x5_cong_0, y5_cong_0, z5_cong_1, x4_cong_1, x6_cong_1]
          · by_cases z5_cong_0 : ((z + 5) % 2 = 0)
            · simp [op_1701_4587, x5_cong_0, y5_cong_0, z5_cong_0, x4_cong_1, x6_cong_1]
            · have z5_cong_1 : (z + 5) % 2 = 1 := Nat.mod_two_ne_zero.mp z5_cong_0
              simp [op_1701_4587, x5_cong_0, y5_cong_0, z5_cong_1, x4_cong_1, x6_cong_1]
        · have x5_cong_1 : (x + 5) % 2 = 1 := Nat.mod_two_ne_zero.mp x5_cong_0
          have x4_cong_0 : (x + 4) % 2 = 0 := mod_two_pred_1_0_to _ x5_cong_1
          have x6_cong_0 : (x + 6) % 2 = 0 := mod_two_succ_1_0_from _ x5_cong_1
          by_cases y5_cong_0 : (y + 5) % 2 = 0
          · by_cases z5_cong_0 : (z + 5) % 2 = 0
            · simp [op_1701_4587
                   ,x5_cong_1,y5_cong_0,z5_cong_0
                   ,x6_cong_0
                   ]
            · have z5_cong_1 : (z + 5) % 2 = 1 := Nat.mod_two_ne_zero.mp z5_cong_0
              simp [op_1701_4587
                   ,x5_cong_1,y5_cong_0,z5_cong_1
                   ,x4_cong_0,x6_cong_0
                   ]
          · have y5_cong_1 : (y + 5) % 2 = 1 := Nat.mod_two_ne_zero.mp y5_cong_0
            by_cases z5_cong_0 : (z + 5) % 2 = 0
            · simp [op_1701_4587
                   ,x5_cong_1,y5_cong_1,z5_cong_0
                   ,x4_cong_0,x6_cong_0
                   ]
            · have z5_cong_1 : (z + 5) % 2 = 1 := Nat.mod_two_ne_zero.mp z5_cong_0
              simp [op_1701_4587
                   ,x5_cong_1,y5_cong_1,z5_cong_1
                   ,x4_cong_0,x6_cong_0
                   ]

    | x+5, 0, 0 | x+5, 0, 1 | x+5, 0, 2 | x+5, 0, 3 | x+5, 0, 4
    | x+5, 1, 0 | x+5, 1, 1 | x+5, 1, 2 | x+5, 1, 3 | x+5, 1, 4
    | x+5, 2, 0 | x+5, 2, 1 | x+5, 2, 2 | x+5, 2, 3 | x+5, 2, 4
    | x+5, 3, 0 | x+5, 3, 1 | x+5, 3, 2 | x+5, 3, 3 | x+5, 3, 4
    | x+5, 4, 0 | x+5, 4, 1 | x+5, 4, 2 | x+5, 4, 3 | x+5, 4, 4
    | 0, 0, x+5 | 0, 1, x+5 | 0, 2, x+5 | 0, 3, x+5 | 0, 4, x+5
    | 1, 0, x+5 | 1, 1, x+5 | 1, 2, x+5 | 1, 3, x+5 | 1, 4, x+5
    | 2, 0, x+5 | 2, 1, x+5 | 2, 2, x+5 | 2, 3, x+5 | 2, 4, x+5
    | 3, 0, x+5 | 3, 1, x+5 | 3, 2, x+5 | 3, 3, x+5 | 3, 4, x+5
    | 4, 0, x+5 | 4, 1, x+5 | 4, 2, x+5 | 4, 3, x+5 | 4, 4, x+5
    | 0, x+5, 0 | 0, x+5, 1 | 0, x+5, 2 | 0, x+5, 3 | 0, x+5, 4
    | 1, x+5, 0 | 1, x+5, 1 | 1, x+5, 2 | 1, x+5, 3 | 1, x+5, 4
    | 2, x+5, 0 | 2, x+5, 1 | 2, x+5, 2 | 2, x+5, 3 | 2, x+5, 4
    | 3, x+5, 0 | 3, x+5, 1 | 3, x+5, 2 | 3, x+5, 3 | 3, x+5, 4
    | 4, x+5, 0 | 4, x+5, 1 | 4, x+5, 2 | 4, x+5, 3 | 4, x+5, 4 =>
      by_cases x5_cong_0 : (x + 5) % 2 = 0
      · have x4_cong_1 : (x + 4) % 2 = 1 := mod_two_pred_0_1_to _ x5_cong_0
        have x6_cong_1 : (x + 6) % 2 = 1 := mod_two_succ_0_1_from _ x5_cong_0
        simp [op_1701_4587,x5_cong_0,x4_cong_1,x6_cong_1]
      · have x5_cong_1 : (x + 5) % 2 = 1 := Nat.mod_two_ne_zero.mp x5_cong_0
        have x4_cong_0 : (x + 4) % 2 = 0 := mod_two_pred_1_0_to _ x5_cong_1
        have x6_cong_0 : (x + 6) % 2 = 0 := mod_two_succ_1_0_from _ x5_cong_1
        simp [op_1701_4587,x5_cong_1,x4_cong_0,x6_cong_0]


    | x+5, y+5, 0 | x+5, y+5, 1 | x+5, y+5, 2 | x+5, y+5, 3 | x+5, y+5, 4
    | x+5, 0, y+5 | x+5, 1, y+5 | x+5, 2, y+5 | x+5, 3, y+5 | x+5, 4, y+5
    | 0, x+5, y+5 | 1, x+5, y+5 | 2, x+5, y+5 | 3, x+5, y+5 | 4, x+5, y+5 =>
        by_cases x5_cong_0 : ((x + 5) % 2 = 0)
        · have x4_cong_1 : (x + 4) % 2 = 1 := mod_two_pred_0_1_to _ x5_cong_0
          have x6_cong_1 : (x + 6) % 2 = 1 := mod_two_succ_0_1_from _ x5_cong_0
          by_cases y5_cong_0 : ((y + 5) % 2 = 0)
          · simp [op_1701_4587,x5_cong_0,y5_cong_0,x4_cong_1,x6_cong_1]
          · have y5_cong_1 : (y + 5) % 2 = 1 := Nat.mod_two_ne_zero.mp y5_cong_0
            simp [op_1701_4587,x5_cong_0,y5_cong_1,x4_cong_1,x6_cong_1]
        · have x5_cong_1 : (x + 5) % 2 = 1 := Nat.mod_two_ne_zero.mp x5_cong_0
          have x4_cong_0 : (x + 4) % 2 = 0 := mod_two_pred_1_0_to _ x5_cong_1
          have x6_cong_0 : (x + 6) % 2 = 0 := mod_two_succ_1_0_from _ x5_cong_1
          by_cases y5_cong_0 : ((y + 5) % 2 = 0)
          · simp [op_1701_4587,x5_cong_1,y5_cong_0,x4_cong_0,x6_cong_0]
          · have y5_cong_1 : (y + 5) % 2 = 1 := Nat.mod_two_ne_zero.mp y5_cong_0
            simp [op_1701_4587,x5_cong_1,y5_cong_1,x4_cong_0,x6_cong_0]

@[equational_result]
theorem Equation1701_not_implies_Equation4587 :
  ∃ (G : Type) (_ : Magma G), Equation1701 G ∧ ¬ Equation4587 G := by
  let magN : Magma ℕ := ⟨fun x y ↦ op_1701_4587 x y⟩
  use ℕ, magN
  simp only [Equation4587, not_forall, magN, op_1701_4587]
  exact And.intro op_1701_4587_satisfies_1701 (by exists 0, 1)
