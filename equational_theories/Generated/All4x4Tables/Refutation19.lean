
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,0,3],[3,2,1,2],[1,2,2,2],[2,2,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,0,3],[3,2,1,2],[1,2,2,2],[2,2,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,0,3],[3,2,1,2],[1,2,2,2],[2,2,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,0,3],[3,2,1,2],[1,2,2,2],[2,2,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [11, 101, 105, 107, 844, 1042, 1045, 3282, 3891] [10, 100, 104, 108, 359, 413, 426, 427, 429, 430, 437, 439, 819, 832, 833, 836, 845, 1023, 1035, 1038, 1046, 1048, 1053, 1060, 1223, 1834, 1847, 1850, 1851, 1860, 3255, 3306, 3316, 3318, 3660, 3661, 3724, 3864, 3865, 3867, 3925, 4065, 4098, 4131, 4269, 4314, 4318, 4583, 4598, 4606, 4611, 4620, 4631, 4647, 4673] :=
    ⟨Fin 4, «FinitePoly [[2,0,0,3],[3,2,1,2],[1,2,2,2],[2,2,3,2]]», by decideFin!⟩
