
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 1, 1], [2, 3, 0, 0], [2, 2, 3, 2], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 1, 1], [2, 3, 0, 0], [2, 2, 3, 2], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 1, 1], [2, 3, 0, 0], [2, 2, 3, 2], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 1, 1], [2, 3, 0, 0], [2, 2, 3, 2], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1853, 1855, 1863, 1865] [8, 99, 361, 362, 364, 365, 375, 377, 378, 385, 411, 817, 1020, 1223, 3253, 3664, 3667, 3668, 3674, 3675, 3678, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3862, 4081] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 1, 1], [2, 3, 0, 0], [2, 2, 3, 2], [3, 3, 3, 3]]», by decideFin!⟩
