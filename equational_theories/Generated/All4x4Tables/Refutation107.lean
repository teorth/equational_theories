
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,2,3],[3,3,3,3],[1,2,3,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,2,3],[3,3,3,3],[1,2,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,2,3],[3,3,3,3],[1,2,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,2,3],[3,3,3,3],[1,2,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2372, 2406] [211, 1631, 1644, 1647, 1657, 1721, 2253, 2269, 2277, 2293, 2300, 2303, 2333, 2443, 2476, 2480, 2484, 2517, 2558, 2571, 2588, 2646, 2699, 2778, 3052, 3068, 3078, 3105, 3115, 3142, 3255, 3261, 3271, 3306, 3456, 3659, 4070, 4090, 4118, 4128, 4131, 4155, 4269, 4320, 4606, 4631] :=
    ⟨Fin 4, «FinitePoly [[1,3,2,3],[3,3,3,3],[1,2,3,3],[0,1,2,3]]», by decideFin!⟩
