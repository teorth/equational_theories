import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,1,1,1],[3,1,0,1],[3,1,1,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[3,1,1,1],[3,1,0,1],[3,1,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[3,1,1,1],[3,1,0,1],[3,1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[3,1,1,1],[3,1,0,1],[3,1,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4303,4328,4376] [4268,4269,4270,4271,4273,4274,4275,4276,4277,4278,4279,4280,4281,4282,4284,4285,4286,4287,4288,4289,4290,4292,4294,4295,4296,4297,4298,4299,4301,4302,4304,4305,4306,4307,4308,4309,4310,4311,4312,4313,4314,4315,4316,4317,4318,4319,4320,4322,4323,4324,4325,4326,4327,4329,4331,4332,4333,4334,4335,4336,4337,4338,4339,4340,4341,4342,4343,4344,4345,4346,4347,4348,4349,4350,4352,4353,4354,4355,4356,4357,4359,4360,4361,4362,4363,4364,4365,4366,4367,4368,4369,4370,4371,4372,4373,4375,4377,4378,4379] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[3,1,1,1],[3,1,0,1],[3,1,1,1]]», by decideFin!⟩
