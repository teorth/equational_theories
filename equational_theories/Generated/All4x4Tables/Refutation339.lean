import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3681,3695,3707,4417,4429] [3671,3673,3676,3680,3683,3696,3697,3702,3705,3706,3708,3710,4436,4440,4450,4457,4467,4585,4587,4589,4593,4595,4596,4605,4607,4610,4612,4613,4614,4615,4617,4618,4619,4621,4624,4625,4627,4628,4629,4633,4635,4637,4638,4640,4641,4642,4643,4644,4645,4646,4648,4649,4650,4652,4653,4656,4658,4659,4660,4661,4662,4663,4664,4665,4666,4667,4668,4669,4670,4671,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694] :=
    ⟨Fin 4, «FinitePoly [[3,0,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]», by decideFin!⟩
