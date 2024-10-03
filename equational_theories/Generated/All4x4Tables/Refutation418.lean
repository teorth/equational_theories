import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1,3],[3,0,1,0],[3,3,0,1],[1,0,3,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1,3],[3,0,1,0],[3,3,0,1],[1,0,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,1,3],[3,0,1,0],[3,3,0,1],[1,0,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1,3],[3,0,1,0],[3,3,0,1],[1,0,3,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3748,3752,3756] [43,3253,3256,3259,3261,3269,3271,3278,3282,3286,3294,3297,3306,3308,3315,3319,3323,3331,3334,3342,3346,3350,3353,3355,3364,3370,3385,3388,3398,3404,3414,3417,3456,3459,3462,3464,3472,3474,3481,3485,3489,3497,3500,3509,3511,3518,3522,3526,3534,3537,3545,3549,3553,3556,3558,3567,3573,3588,3591,3601,3607,3617,3620,3761,3770,3794,4065,4068,4073,4081,4090,4094,4098,4109,4118,4127,4131,4135,4146,4165,4210,4226,4273,4320,4325,4332,4362,4380,4435,4585,4605,4612,4656,4684] :=
    ⟨Fin 4, «FinitePoly [[0,1,1,3],[3,0,1,0],[3,3,0,1],[1,0,3,0]]», by decideFin!⟩
