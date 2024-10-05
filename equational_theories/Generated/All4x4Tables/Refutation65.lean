
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,3],[3,3,0,3],[2,0,3,3],[3,0,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,3,3],[3,3,0,3],[2,0,3,3],[3,0,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,3,3],[3,3,0,3],[2,0,3,3],[3,0,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,3,3],[3,3,0,3],[2,0,3,3],[3,0,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3280, 3478, 3696, 3703, 4611] [323, 3259, 3261, 3269, 3271, 3318, 3319, 3343, 3511, 3519, 3666, 3669, 3670, 3698, 3862, 4065, 4268, 4269, 4275, 4284, 4291, 4314, 4320, 4321, 4332, 4380, 4583, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,0,3,3],[3,3,0,3],[2,0,3,3],[3,0,3,3]]», by decideFin!⟩
