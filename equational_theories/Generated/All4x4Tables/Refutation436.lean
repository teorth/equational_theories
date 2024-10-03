import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,2,3],[3,2,2,3],[2,2,2,2],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,2,3],[3,2,2,3],[2,2,2,2],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,2,3],[3,2,2,3],[2,2,2,2],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,2,3],[3,2,2,3],[2,2,2,2],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3520,3919,3926] [308,326,327,3254,3255,3256,3257,3309,3315,3317,3319,3320,3321,3322,3323,3324,3458,3459,3460,3521,3522,3523,3524,3525,3526,3527,3864,3865,3866,3927,3928,3929,3930,3931,3932,3933,4268,4282,4314,4315,4339,4357,4395,4396,4397,4472,4473,4474,4510,4511,4512,4513] :=
    ⟨Fin 4, «FinitePoly [[3,3,2,3],[3,2,2,3],[2,2,2,2],[3,3,3,3]]», by decideFin!⟩
