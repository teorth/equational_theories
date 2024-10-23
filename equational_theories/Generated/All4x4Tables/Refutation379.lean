
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1,0],[1,1,1,0],[1,2,2,1],[2,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1,0],[1,1,1,0],[1,2,2,1],[2,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,1,0],[1,1,1,0],[1,2,2,1],[2,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1,0],[1,1,1,0],[1,2,2,1],[2,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [824] [825, 826, 1026, 1029, 1226, 1228, 1229, 1231, 1232, 1632, 2449, 3315, 3316, 3459, 3518, 3519, 3521, 3714, 3721, 3724, 3725, 3924, 3925, 3927, 3928, 4120, 4121, 4127, 4128, 4130, 4131, 4314, 4433, 4435, 4436, 4472, 4473, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[0,0,1,0],[1,1,1,0],[1,2,2,1],[2,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
