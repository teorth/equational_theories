
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 0, 1], [1, 0, 3, 1], [2, 0, 0, 2], [1, 3, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 0, 1], [1, 0, 3, 1], [2, 0, 0, 2], [1, 3, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 0, 1], [1, 0, 3, 1], [2, 0, 0, 2], [1, 3, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 0, 1], [1, 0, 3, 1], [2, 0, 0, 2], [1, 3, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [10, 99, 378, 458, 1031, 1041, 1051, 1055, 1059, 1063, 1225, 1228, 1231, 1238, 1241, 1248, 1251, 1834, 1847, 1850, 3255, 3316, 3864, 3867, 3870, 3925, 4269, 4284] [3, 13, 23, 47, 151, 203, 255, 307, 375, 614, 817, 1426, 1629, 2035, 2238, 2441, 2644, 2847, 3050, 3258, 3261, 3456, 3659, 3873, 3928, 4118, 4121, 4128, 4287, 4380, 4599] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 0, 1], [1, 0, 3, 1], [2, 0, 0, 2], [1, 3, 3, 1]]», by decideFin!⟩
