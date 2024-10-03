import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,1,1],[3,1,1,1],[1,3,3,3],[1,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,1,1],[3,1,1,1],[1,3,3,3],[1,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,1,1],[3,1,1,1],[1,3,3,3],[1,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,1,1],[3,1,1,1],[1,3,3,3],[1,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4440,4516,4521] [4381,4382,4384,4396,4397,4398,4400,4401,4402,4404,4433,4434,4435,4437,4438,4439,4441,4470,4471,4472,4474,4475,4476,4478,4507,4508,4509,4510,4512,4513,4514,4515,4517,4518,4519,4520,4522,4583,4584,4586,4597,4599,4600,4601,4602,4603,4604,4629,4630,4631,4632,4633,4634,4654,4655,4657,4672,4674,4675,4676] :=
    ⟨Fin 4, «FinitePoly [[2,1,1,1],[3,1,1,1],[1,3,3,3],[1,3,3,3]]», by decideFin!⟩
