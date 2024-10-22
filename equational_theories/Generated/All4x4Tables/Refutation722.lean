
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,4,4,0,0,0,2],[4,6,4,1,6,1,1,1],[1,3,2,2,7,2,3,3],[1,3,3,3,7,3,3,3],[4,5,5,2,4,4,4,2],[5,5,5,5,5,0,7,3],[6,6,4,6,6,0,6,6],[1,7,4,7,6,4,7,7]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,4,4,0,0,0,2],[4,6,4,1,6,1,1,1],[1,3,2,2,7,2,3,3],[1,3,3,3,7,3,3,3],[4,5,5,2,4,4,4,2],[5,5,5,5,5,0,7,3],[6,6,4,6,6,0,6,6],[1,7,4,7,6,4,7,7]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[1,2,4,4,0,0,0,2],[4,6,4,1,6,1,1,1],[1,3,2,2,7,2,3,3],[1,3,3,3,7,3,3,3],[4,5,5,2,4,4,4,2],[5,5,5,5,5,0,7,3],[6,6,4,6,6,0,6,6],[1,7,4,7,6,4,7,7]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,4,4,0,0,0,2],[4,6,4,1,6,1,1,1],[1,3,2,2,7,2,3,3],[1,3,3,3,7,3,3,3],[4,5,5,2,4,4,4,2],[5,5,5,5,5,0,7,3],[6,6,4,6,6,0,6,6],[1,7,4,7,6,4,7,7]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [834] [1020, 1224, 1225, 1229, 1239, 1241, 1242, 1249, 1251, 1252, 1832, 3253, 3659, 3864, 3865, 3867, 3870, 3915, 3925, 3928, 4065, 4269, 4270, 4314, 4583, 4598, 4631] :=
    ⟨Fin 8, «FinitePoly [[1,2,4,4,0,0,0,2],[4,6,4,1,6,1,1,1],[1,3,2,2,7,2,3,3],[1,3,3,3,7,3,3,3],[4,5,5,2,4,4,4,2],[5,5,5,5,5,0,7,3],[6,6,4,6,6,0,6,6],[1,7,4,7,6,4,7,7]]», Finite.of_fintype _, by decideFin!⟩
