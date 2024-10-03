import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,2,1],[3,3,3,3],[3,3,3,3],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,2,1],[3,3,3,3],[3,3,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,2,1],[3,3,3,3],[3,3,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,2,1],[3,3,3,3],[3,3,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3465,3466,3467,3468,3469,3470] [307,308,309,310,311,323,3253,3254,3255,3256,3257,3258,3259,3260,3261,3262,3263,3264,3265,3266,3267,3306,3308,3309,3509,3519,3521,3522,3525,3529,3537,3659,3664,3712,4065,4070,4118,4128,4131,4138,4269,4270,4316,4341,4380] :=
    ⟨Fin 4, «FinitePoly [[1,2,2,1],[3,3,3,3],[3,3,3,3],[3,3,3,3]]», by decideFin!⟩
