
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 2, 3], [2, 3, 3, 2], [3, 2, 2, 3], [2, 3, 3, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 2, 3], [2, 3, 3, 2], [3, 2, 2, 3], [2, 3, 3, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 2, 3], [2, 3, 3, 2], [3, 2, 2, 3], [2, 3, 3, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 2, 3], [2, 3, 3, 2], [3, 2, 2, 3], [2, 3, 3, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3278, 3319, 3388, 4068, 4143] [8, 23, 411, 1020, 1629, 1832, 2441, 3050, 3255, 3256, 3456, 3862, 4109] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 2, 3], [2, 3, 3, 2], [3, 2, 2, 3], [2, 3, 3, 2]]», by decideFin!⟩
