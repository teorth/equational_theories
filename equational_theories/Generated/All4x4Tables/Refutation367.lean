
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,1],[3,3,1,2],[2,3,3,0],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,0,3,1],[3,3,1,2],[2,3,3,0],[3,3,3,3]]» : Magma (Fin 4) where
  op := finOpTable "[[3,0,3,1],[3,3,1,2],[2,3,3,0],[3,3,3,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,0,3,1],[3,3,1,2],[2,3,3,0],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [371, 626] [56, 99, 151, 203, 255, 411, 619, 629, 630, 632, 633, 639, 640, 642, 643, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3714, 3721, 3722, 3724, 3725, 3915, 3918, 3925, 3927, 3928, 4073, 4081, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4268, 4269, 4314, 4380, 4599, 4629, 4673] :=
    ⟨Fin 4, «All4x4Tables [[3,0,3,1],[3,3,1,2],[2,3,3,0],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
