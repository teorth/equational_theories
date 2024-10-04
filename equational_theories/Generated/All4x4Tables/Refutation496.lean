
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,4,1],[1,3,0,2,4],[2,1,4,0,3],[3,4,2,1,0],[4,0,1,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,4,1],[1,3,0,2,4],[2,1,4,0,3],[3,4,2,1,0],[4,0,1,3,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,3,4,1],[1,3,0,2,4],[2,1,4,0,3],[3,4,2,1,0],[4,0,1,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,4,1],[1,3,0,2,4],[2,1,4,0,3],[3,4,2,1,0],[4,0,1,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1276, 1285] [8, 419, 436, 466, 500, 528, 575, 614, 817, 1020, 1028, 1038, 1045, 1075, 1082, 1109, 1122, 1231, 1241, 1248, 1312, 1316, 1325, 1426, 1543, 1577, 1590, 1629, 1832, 2035, 2053, 2060, 2090, 2097, 2124, 2137, 2238, 2441, 2592, 2605, 2644, 2847, 3050, 3068, 3075, 3105, 3112, 3139, 3152, 3253, 3456, 3591, 3659, 3862, 4065, 4118, 4131, 4158, 4165, 4275, 4320, 4380, 4622, 4635, 4647] :=
    ⟨Fin 5, «FinitePoly [[0,2,3,4,1],[1,3,0,2,4],[2,1,4,0,3],[3,4,2,1,0],[4,0,1,3,2]]», by decideFin!⟩
