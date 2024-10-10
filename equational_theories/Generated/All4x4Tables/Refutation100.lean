
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
def «FinitePoly [[3,0,3,1],[3,3,1,2],[2,3,3,0],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,3,1],[3,3,1,2],[2,3,3,0],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,3,1],[3,3,1,2],[2,3,3,0],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [361, 626, 4107, 4598] [56, 99, 151, 203, 255, 411, 619, 629, 630, 632, 633, 639, 640, 642, 643, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3664, 3667, 3668, 3712, 3714, 3721, 3722, 3724, 3725, 3863, 3865, 3868, 3871, 3915, 3917, 3918, 3925, 3927, 3928, 4073, 4074, 4081, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4268, 4269, 4283, 4284, 4314, 4380, 4585, 4599, 4629, 4673] :=
    ⟨Fin 4, «FinitePoly [[3,0,3,1],[3,3,1,2],[2,3,3,0],[3,3,3,3]]», by decideFin!⟩
