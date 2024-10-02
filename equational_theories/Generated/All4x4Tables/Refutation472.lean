
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [341, 345, 349, 354, 355, 383, 393, 397, 401, 404, 406, 3455, 3626, 3658, 3850, 3855, 3858, 3859, 4032, 4064, 4235, 4267, 4370, 4377, 4537, 4556, 4566, 4568, 4581, 4685] [2, 3, 8, 23, 47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3]]», by decideFin!⟩
