import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,0,3],[3,3,2,3],[3,0,3,1],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,0,3],[3,3,2,3],[3,0,3,1],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,0,3],[3,3,2,3],[3,0,3,1],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,0,3],[3,3,2,3],[3,0,3,1],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [208,211,221,2476,2571,2709,2724] [218,231,246,307,312,323,2238,2243,2246,2253,2256,2263,2266,2281,2290,2293,2303,2318,2327,2330,2340,2355,2364,2368,2385,2402,2406,2430,2506,2588,2672,2812,3065,3068,3253,3306,3461,4070] :=
    ⟨Fin 4, «FinitePoly [[3,1,0,3],[3,3,2,3],[3,0,3,1],[0,1,2,3]]», by decideFin!⟩
