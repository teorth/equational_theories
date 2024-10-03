import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[2,3,3,2],[3,3,1,1],[1,2,1,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[2,3,3,2],[3,3,1,1],[1,2,1,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[2,3,3,2],[3,3,1,1],[1,2,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[2,3,3,2],[3,3,1,1],[1,2,1,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4154] [43,307,323,325,326,332,333,335,359,375,377,378,384,385,387,3309,3319,3345,3512,3522,3546,3548,3555,3659,3715,3722,3724,3749,3751,3758,3915,3918,3927,3961,4118,4121,4130,4164,4284,4291,4293,4343,4399,4406,4436,4445,4470,4472,4479,4599,4608,4629,4658] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[2,3,3,2],[3,3,1,1],[1,2,1,2]]», by decideFin!⟩
