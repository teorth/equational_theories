import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,3,1],[3,2,2,0],[3,2,2,0],[1,0,0,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,3,1],[3,2,2,0],[3,2,2,0],[1,0,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,3,1],[3,2,2,0],[3,2,2,0],[1,0,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,3,1],[3,2,2,0],[3,2,2,0],[1,0,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3364,3370,3553,3567,4013,4026,4182,4216] [3278,3414,3417,3472,3588,3601,3878,3994,4007,4068,4135,4162,4273,4275,4305,4307,4332,4383,4386,4409,4413,4421,4446,4450,4458,4585,4588,4640,4647,4656] :=
    ⟨Fin 4, «FinitePoly [[0,3,3,1],[3,2,2,0],[3,2,2,0],[1,0,0,3]]», by decideFin!⟩
