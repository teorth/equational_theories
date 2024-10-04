
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,1,1],[2,3,2,3],[3,1,3,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,1,1],[2,3,2,3],[3,1,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,1,1],[2,3,2,3],[3,1,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,1,1],[2,3,2,3],[3,1,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3197, 3509] [203, 1629, 2238, 2441, 2571, 2588, 2605, 2646, 2652, 2672, 2696, 2699, 2706, 2709, 2733, 2736, 3052, 3058, 3068, 3078, 3105, 3139, 3142, 3255, 3258, 3261, 3268, 3271, 3278, 3458, 3481, 3519, 3522, 3659, 4065, 4090, 4118, 4128, 4131, 4155, 4165, 4269, 4272, 4320, 4606, 4611, 4622, 4631] :=
    ⟨Fin 4, «FinitePoly [[1,1,1,1],[2,3,2,3],[3,1,3,3],[0,1,2,3]]», by decideFin!⟩
