import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,1,3],[3,3,2,0],[3,3,3,3],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,1,3],[3,3,2,0],[3,3,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,1,3],[3,3,2,0],[3,3,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,1,3],[3,3,2,0],[3,3,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4075,4082,4085,4087,4101,4107,4108,4111,4113] [3862,3865,3870,3878,3887,3891,3895,3906,4078,4079,4088,4100,4115,4585,4586,4598,4599,4600,4601,4602,4603,4604,4629,4630,4632,4633,4634,4654,4655,4656,4657,4672,4673,4674,4675,4676] :=
    ⟨Fin 4, «FinitePoly [[3,2,1,3],[3,3,2,0],[3,3,3,3],[3,3,3,3]]», by decideFin!⟩
