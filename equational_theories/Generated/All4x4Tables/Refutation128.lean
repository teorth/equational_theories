import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0,1],[2,1,1,0],[1,2,3,3],[3,3,2,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0,1],[2,1,1,0],[1,2,3,3],[3,3,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,0,1],[2,1,1,0],[1,2,3,3],[3,3,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0,1],[2,1,1,0],[1,2,3,3],[3,3,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [325] [326,359,375,377,378,3306,3308,3309,3315,3318,3319,3509,3511,3512,3519,3521,3659,3712,3714,3715,3721,3722,3724,3725,3862,3915,3917,3918,3924,3925,3927,3928,4283,4284,4314,4358,4599,4629] :=
    ⟨Fin 4, «FinitePoly [[0,0,0,1],[2,1,1,0],[1,2,3,3],[3,3,2,2]]», by decideFin!⟩
