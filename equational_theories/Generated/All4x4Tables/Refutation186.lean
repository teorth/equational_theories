import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,3],[3,2,2,1],[1,1,2,3],[0,1,0,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,3],[3,2,2,1],[1,1,2,3],[0,1,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,3],[3,2,2,1],[1,1,2,3],[0,1,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,3],[3,2,2,1],[1,1,2,3],[0,1,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3105] [2530,2533,2536,2554,2571,2588,2623,2646,2659,2665,2672,2687,2696,2702,2709,2712,2724,2736,2739,2770,2774,2778,2782,2791,2812,2836,3052,3065,3071,3078,3093,3115,3142,3145,3180,3197,3264,3519,3525,3529,3749,3769,3786,4128,4138,4155,4175,4606,4611] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,3],[3,2,2,1],[1,1,2,3],[0,1,0,3]]», by decideFin!⟩
