import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,1],[3,3,3,3],[2,3,3,1],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,1],[3,3,3,3],[2,3,3,1],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,1],[3,3,3,3],[2,3,3,1],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,1],[3,3,3,3],[2,3,3,1],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3869,3872,3873,3874,3875,3876,3879,3882,3885,3886,3889,3892,3896,3899,3900,3904,3907,3908,3909,3911,3912,3913,4076,4104,4105,4583,4592,4594,4597,4601,4609,4616,4620,4623,4626,4639,4651] [3664,3666,3668,3669,3670,3671,3672,3673,3674,3676,3678,3679,3680,3681,3682,3683,3694,3695,3696,3697,3698,3699,3701,3702,3704,3705,3706,3707,3708,3709,3710,4269,4314,4316,4318,4587,4593,4599,4602,4673] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,1],[3,3,3,3],[2,3,3,1],[3,3,3,3]]», by decideFin!⟩
