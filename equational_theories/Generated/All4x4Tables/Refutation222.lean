
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 1, 1, 1], [2, 3, 2, 3], [3, 1, 3, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 1, 1, 1], [2, 3, 2, 3], [3, 1, 3, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 1, 1, 1], [2, 3, 2, 3], [3, 1, 3, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 1, 1, 1], [2, 3, 2, 3], [3, 1, 3, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2659, 3197, 4314] [23, 203, 255, 312, 1629, 2238, 2441, 2646, 2652, 2669, 2672, 2696, 2699, 2706, 2709, 2733, 2736, 2847, 3052, 3055, 3058, 3068, 3078, 3079, 3105, 3139, 3142, 3258, 3268, 3278, 3458, 3519, 3521, 3522, 3659, 4065, 4272, 4584, 4590, 4606] :=
    ⟨Fin 4, «FinitePoly [[1, 1, 1, 1], [2, 3, 2, 3], [3, 1, 3, 3], [0, 1, 2, 3]]», by decideFin!⟩
