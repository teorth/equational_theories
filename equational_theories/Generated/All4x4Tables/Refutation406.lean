import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,3,1,3],[3,0,1,3],[3,3,1,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,3],[3,3,1,3],[3,0,1,3],[3,3,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,3],[3,3,1,3],[3,0,1,3],[3,3,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,3],[3,3,1,3],[3,0,1,3],[3,3,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4295,4345,4371] [4268,4270,4271,4272,4273,4274,4275,4276,4277,4278,4279,4280,4281,4282,4283,4285,4286,4288,4289,4291,4292,4294,4296,4297,4298,4299,4300,4301,4302,4303,4304,4305,4306,4307,4308,4309,4310,4311,4312,4313,4314,4315,4317,4318,4319,4320,4321,4322,4323,4324,4325,4326,4327,4328,4329,4330,4331,4332,4333,4334,4335,4336,4337,4338,4339,4341,4342,4344,4346,4347,4348,4349,4350,4351,4352,4353,4354,4355,4356,4357,4358,4359,4361,4362,4363,4364,4365,4366,4367,4368,4370,4372,4373,4374,4375,4376,4377,4378,4379] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,3],[3,3,1,3],[3,0,1,3],[3,3,1,3]]», by decideFin!⟩
