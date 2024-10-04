
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,2,1],[3,0,2,1],[3,0,2,1],[3,0,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,2,1],[3,0,2,1],[3,0,2,1],[3,0,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,2,1],[3,0,2,1],[3,0,2,1],[3,0,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,2,1],[3,0,2,1],[3,0,2,1],[3,0,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [39, 94] [50, 53, 56, 99, 151, 203, 255, 411, 615, 617, 620, 623, 630, 633, 640, 643, 818, 820, 823, 826, 833, 836, 843, 846, 1020, 1223, 1427, 1429, 1432, 1435, 1442, 1445, 1452, 1455, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3865, 3868, 3871, 3917, 3927, 4066, 4068, 4071, 4074, 4120, 4127, 4130, 4268, 4270, 4283, 4314, 4380, 4583, 4585, 4598, 4629] :=
    ⟨Fin 4, «FinitePoly [[3,0,2,1],[3,0,2,1],[3,0,2,1],[3,0,2,1]]», by decideFin!⟩
