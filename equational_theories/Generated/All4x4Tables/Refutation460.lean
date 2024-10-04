import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,1],[3,1,1,3],[1,1,2,2],[2,3,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,1],[3,1,1,3],[1,1,2,2],[2,3,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,1],[3,1,1,3],[1,1,2,2],[2,3,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,1],[3,1,1,3],[1,1,2,2],[2,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3961] [43,307,323,325,326,332,333,335,359,375,377,378,384,385,387,3253,3306,3308,3309,3315,3316,3318,3319,3342,3343,3345,3346,3352,3353,3355,3509,3512,3519,3548,3555,3918,3925,3954,4065,4128,4130,4155,4157,4283,4358,4380,4398,4405,4435,4442,4482,4531,4544,4635,4677] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,1],[3,1,1,3],[1,1,2,2],[2,3,2,3]]», by decideFin!⟩
