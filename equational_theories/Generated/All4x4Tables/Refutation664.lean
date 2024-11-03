
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,0,4,0],[1,1,1,1,1],[3,4,2,2,2],[4,3,4,3,3],[4,4,4,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,0,4,0],[1,1,1,1,1],[3,4,2,2,2],[4,3,4,3,3],[4,4,4,4,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,0,4,0],[1,1,1,1,1],[3,4,2,2,2],[4,3,4,3,3],[4,4,4,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,0,4,0],[1,1,1,1,1],[3,4,2,2,2],[4,3,4,3,3],[4,4,4,4,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1233] [822, 1025, 1028, 1225, 1229, 1631, 2446, 3315, 3316, 3458, 3518, 3519, 3521, 3714, 3721, 3724, 3725, 3924, 3925, 3927, 3928, 4120, 4121, 4127, 4128, 4130, 4131, 4314, 4433, 4435, 4436, 4472, 4473, 4598, 4599, 4629] :=
    ⟨Fin 5, «FinitePoly [[0,2,0,4,0],[1,1,1,1,1],[3,4,2,2,2],[4,3,4,3,3],[4,4,4,4,4]]», Finite.of_fintype _, by decideFin!⟩
