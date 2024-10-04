
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,3,3],[3,3,2,2],[1,1,0,0],[0,0,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,3,3],[3,3,2,2],[1,1,0,0],[0,0,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,3,3],[3,3,2,2],[1,1,0,0],[0,0,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,3,3],[3,3,2,2],[1,1,0,0],[0,0,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [161, 215, 3083, 3091, 3094, 3527, 4357] [38, 153, 154, 156, 157, 204, 206, 208, 211, 307, 359, 1431, 1432, 1434, 1435, 1441, 1442, 1444, 1445, 1629, 1832, 2035, 2050, 2051, 2053, 2239, 2241, 2244, 2247, 2253, 2256, 2263, 2266, 2441, 3051, 3052, 3055, 3059, 3065, 3069, 3076, 3078, 3253, 3461, 3462, 3464, 3465, 3509, 3511, 3512, 3659, 3862, 3915, 3918, 4065, 4117, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4269, 4270, 4283, 4284, 4380, 4510, 4511, 4512, 4583, 4584, 4599, 4629, 4636] :=
    ⟨Fin 4, «FinitePoly [[2,2,3,3],[3,3,2,2],[1,1,0,0],[0,0,1,1]]», by decideFin!⟩
