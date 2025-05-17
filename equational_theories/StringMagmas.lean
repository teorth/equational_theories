import equational_theories.Equations.All
import equational_theories.EquationalResult


namespace StringMagmas

private abbrev M : Type := List Nat

private def M.mul (a b : M) : M :=
  if a = b then b else
  if (b ++ b ++ b) <:+ a then b else a ++ b

scoped infix:70 " * " => M.mul

private theorem M.mul_def (a b : M) : a * b =
    if a = b then b else
    if (b ++ b ++ b) <:+ a then b else a ++ b :=
  rfl

@[simp]
private theorem M.mul_self (a : M) : a * a = a := by
  simp [M.mul_def a a, if_pos]

private theorem Msat3102 (x y : M) : x = (((y * x) * x) * x) * x := by
  rw [M.mul_def y x]
  split
  · next h => simp
  next h =>
  split
  · next h => simp
  rw [M.mul_def (y ++ x) x]
  split
  · next h => simp
  next h =>
  split
  · next h => simp
  rw [M.mul_def (y ++ x ++ x) x]
  split
  · next h => simp
  next h =>
  split
  · next h => simp
  rw [M.mul_def _ x]
  split
  · next h => simp
  next h =>
  rw [if_pos]
  repeat rw [List.append_assoc]
  exact List.suffix_append y (x ++ (x ++ x))

/-- `M` does not satisfy 3176 -/
private theorem Mnot3176 : ∃ (x y z : M), x ≠ (((y * z) * x) * x) * x := by
  exists [0], [1], [2]

/-- `M` does not satisfy 270 -/
private theorem Mnot270 : ∃ (x y : M), x ≠ ((y * x) * x) * x := by
  exists [0], [1]

@[equational_result]
theorem Equation3102_not_implies_Equation3176 : ∃ (G: Type) (_: Magma G), Equation3102 G ∧ ¬ Equation3176 G := by
  refine ⟨M, ⟨M.mul⟩, Msat3102, ?_⟩
  · unfold Equation3176
    push_neg
    exact Mnot3176

@[equational_result]
theorem Equation3102_not_implies_Equation270 : ∃ (G: Type) (_: Magma G), Equation3102 G ∧ ¬ Equation270 G := by
  refine ⟨M, ⟨M.mul⟩, Msat3102, ?_⟩
  · unfold Equation270
    push_neg
    exact Mnot270

end StringMagmas
