
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1876, 2939] [159, 231, 411, 1451, 1629, 1857, 2043, 2070, 2087, 2124, 2127, 2134, 2243, 2246, 2253, 2266, 2290, 2300, 2330, 2340, 2441, 2644, 2849, 2852, 2855, 2862, 2865, 2872, 2899, 2909, 2946, 2949, 3052, 3055, 3065, 3139, 3149, 3152, 3253, 3458, 3461, 3464, 3481, 3509, 3512, 3519, 3546, 3661, 3664, 3667, 3674, 3677, 3684, 3712, 3725, 3752, 3759, 3864, 3867, 3870, 3877, 3890, 3918, 3925, 3928, 3952, 4067, 4070, 4090, 4093, 4121, 4128, 4155, 4165, 4269, 4270, 4272, 4284, 4291, 4320, 4396, 4399, 4445, 4473, 4480, 4584, 4587, 4590, 4598, 4599, 4606] :=
    ⟨Fin 4, «FinitePoly [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]», Finite.of_fintype _, by decideFin!⟩
