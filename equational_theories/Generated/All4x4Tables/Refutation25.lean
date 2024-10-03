import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,3],[3,3,0,3],[1,3,1,3],[0,3,1,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,3],[3,3,0,3],[1,3,1,3],[0,3,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,3],[3,3,0,3],[1,3,1,3],[0,3,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,3],[3,3,0,3],[1,3,1,3],[0,3,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3893,4093] [3870,3877,3905,4067,4070,4076,4080,4086,4090,4096,4100,4104,4108,4112,4269,4316,4587,4590,4593,4599,4606,4611,4615,4619,4622,4625,4635,4638,4642,4645,4649,4663,4666,4669,4677,4682,4689,4693] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,3],[3,3,0,3],[1,3,1,3],[0,3,1,3]]», by decideFin!⟩
