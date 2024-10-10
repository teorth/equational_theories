
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 2 * y**2 + 0 * x + 0 * y + 1 * x * y) % 3' (0, 39, 306, 309, 311, 315, 319, 3252, 3255, 3257, 3261, 3265, 3267, 3271, 3275, 3277, 3281, 3285, 3287, 3292, 3297, 3302, 3658, 3661, 3663, 3664, 3667, 3671, 3673, 3676, 3677, 3681, 3683, 3687, 3691, 3693, 3698, 3699, 3703, 3708, 4269, 4271, 4275, 4279, 4340, 4342, 4345, 4350, 4354, 4589, 4621)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * y² + x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => 2 * y*y + x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * y² + x * y % 3» :
  ∃ (G : Type) (_ : Magma G), Facts G [316] [3306] :=
    ⟨Fin 3, «FinitePoly 2 * y² + x * y % 3», by decideFin!⟩
