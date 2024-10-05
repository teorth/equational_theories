
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,0,3],[2,1,0,3],[2,1,3,3],[2,1,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,0,3],[2,1,0,3],[2,1,3,3],[2,1,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,0,3],[2,1,0,3],[2,1,3,3],[2,1,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,0,3],[2,1,0,3],[2,1,3,3],[2,1,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1041, 1063, 1664, 1672, 1738, 3268, 3316] [105, 108, 117, 151, 411, 817, 1023, 1036, 1039, 1045, 1046, 1049, 1224, 1225, 1229, 1239, 1242, 1249, 1251, 1252, 1631, 1832, 3256, 3261, 3306, 3309, 3315, 3318, 3319, 3660, 3661, 3662, 3665, 3721, 3724, 3725, 3862, 4065, 4269, 4270, 4284, 4314, 4583, 4584, 4598] :=
    ⟨Fin 4, «FinitePoly [[1,1,0,3],[2,1,0,3],[2,1,3,3],[2,1,0,3]]», by decideFin!⟩
