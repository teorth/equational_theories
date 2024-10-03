import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,0,3],[3,3,1,3],[2,2,3,3],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,0,3],[3,3,1,3],[2,2,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,0,3],[3,3,1,3],[2,2,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,0,3],[3,3,1,3],[2,2,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3483,3487,3490,3889,3893,3896,4412,4417,4421,4429] [3461,3467,3469,3475,3479,3491,3496,3506,3868,3874,3880,3883,3899,3903,3911,4269,4273,4279,4283,4286,4291,4296,4301,4305,4311,4316,4321,4324,4332,4336,4383,4385,4393,4399,4403,4405,4413,4415,4420,4430,4432,4433,4434,4435,4438,4442,4443,4445,4446,4447,4449,4450,4452,4454,4458,4460,4461,4462,4463,4466,4585,4587,4635,4640,4642,4656,4666] :=
    ⟨Fin 4, «FinitePoly [[3,3,0,3],[3,3,1,3],[2,2,3,3],[3,3,3,3]]», by decideFin!⟩
