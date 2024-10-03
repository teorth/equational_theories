import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,1],[3,1,1,0],[0,1,0,3],[1,0,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,1],[3,1,1,0],[0,1,0,3],[1,0,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,1],[3,1,1,0],[0,1,0,3],[1,0,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,1],[3,1,1,0],[0,1,0,3],[1,0,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3417,3601,4007,4162] [3259,3261,3319,3331,3334,3342,3364,3370,3459,3462,3522,3526,3534,3545,3553,3567,3880,3887,3915,3964,3997,4013,4023,4026,4073,4083,4118,4146,4167,4182,4200,4216,4273,4275,4305,4307,4332,4383,4386,4409,4413,4421,4446,4450,4458,4585,4588,4640,4647,4656] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,1],[3,1,1,0],[0,1,0,3],[1,0,3,3]]», by decideFin!⟩
