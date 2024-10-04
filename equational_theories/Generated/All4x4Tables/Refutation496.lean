
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
  ∃ (G : Type) (_ : Magma G), Facts G [1276, 1285] [419, 436, 466, 500, 614, 817, 1020, 1231, 1241, 1248, 1312, 1316, 1325, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4275, 4320, 4380, 4622, 4635, 4647] :=
    ⟨Fin 5, «FinitePoly [[0,2,3,4,1],[1,3,0,2,4],[2,1,4,0,3],[3,4,2,1,0],[4,0,1,3,2]]», by decideFin!⟩
