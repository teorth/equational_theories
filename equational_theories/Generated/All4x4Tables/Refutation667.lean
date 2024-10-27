
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,5,3,0,5,0],[2,1,1,1,1,2],[3,4,2,2,2,3],[3,4,3,3,3,3],[4,3,3,4,4,3],[5,0,0,5,5,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,5,3,0,5,0],[2,1,1,1,1,2],[3,4,2,2,2,3],[3,4,3,3,3,3],[4,3,3,4,4,3],[5,0,0,5,5,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,5,3,0,5,0],[2,1,1,1,1,2],[3,4,2,2,2,3],[3,4,3,3,3,3],[4,3,3,4,4,3],[5,0,0,5,5,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,5,3,0,5,0],[2,1,1,1,1,2],[3,4,2,2,2,3],[3,4,3,3,3,3],[4,3,3,4,4,3],[5,0,0,5,5,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1235] [1026, 1227, 1230, 1233, 1234, 1633, 2452, 3315, 3316, 3460, 3518, 3519, 3521, 3714, 3721, 3724, 3725, 3924, 3925, 3927, 3928, 4120, 4121, 4127, 4128, 4130, 4131, 4314, 4433, 4435, 4436, 4472, 4473, 4598, 4599, 4629] :=
    ⟨Fin 6, «FinitePoly [[0,5,3,0,5,0],[2,1,1,1,1,2],[3,4,2,2,2,3],[3,4,3,3,3,3],[4,3,3,4,4,3],[5,0,0,5,5,5]]», Finite.of_fintype _, by decideFin!⟩
