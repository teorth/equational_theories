
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,2,3],[3,0,3,2],[0,1,2,3],[0,1,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,2,3],[3,0,3,2],[0,1,2,3],[0,1,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,2,3],[3,0,3,2],[0,1,2,3],[0,1,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,2,3],[3,0,3,2],[0,1,2,3],[0,1,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [221, 2277, 2281, 2293, 2340, 2484, 2778] [208, 231, 1629, 2240, 2263, 2290, 2300, 2303, 2327, 2330, 2443, 2446, 2459, 2466, 2496, 2506, 2530, 2533, 2543, 2571, 2588, 2605, 2646, 2652, 2659, 2672, 2699, 2706, 2709, 2733, 3050, 3078, 3105, 3115, 3139, 3142, 3152, 3253, 3456, 3659, 4068, 4070, 4090, 4118, 4128, 4131, 4155, 4165, 4269, 4270, 4272, 4314, 4320, 4606, 4611, 4622, 4631] :=
    ⟨Fin 4, «FinitePoly [[2,0,2,3],[3,0,3,2],[0,1,2,3],[0,1,2,2]]», by decideFin!⟩
