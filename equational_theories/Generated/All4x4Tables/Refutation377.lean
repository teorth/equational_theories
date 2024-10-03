import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,3],[3,1,1,3],[1,3,0,1],[3,1,1,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,1,3],[3,1,1,3],[1,3,0,1],[3,1,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,3],[3,1,1,3],[1,3,0,1],[3,1,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,3],[3,1,1,3],[1,3,0,1],[3,1,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4428] [4269,4272,4278,4284,4287,4291,4296,4300,4304,4310,4316,4323,4327,4330,4334,4340,4348,4351,4354,4360,4367,4374,4378,4432,4435,4438,4442,4445,4448,4452,4456,4460,4464,4470,4473,4476,4480,4483,4486,4490,4494,4498,4502,4508,4512,4516,4520,4525,4529,4533,4537,4542,4546,4550,4554,4559,4564,4569,4574,4579] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,3],[3,1,1,3],[1,3,0,1],[3,1,1,3]]», by decideFin!⟩
