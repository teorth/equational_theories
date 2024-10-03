import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,1],[3,1,2,3],[0,1,2,3],[0,0,0,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,1],[3,1,2,3],[0,1,2,3],[0,0,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,1],[3,1,2,3],[0,1,2,3],[0,0,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,1],[3,1,2,3],[0,1,2,3],[0,0,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [28,218,270,290,1701,1884,2290,2567,2584,2706,2770,2787,2956,2973,3024,3102,3122,3159,3176,3193,3210,3227] [208,333,1025,1847,2243,2253,2300,2446,2466,2476,2513,2649,2716,2804,3346,3353,3546,3759,3803,3867,4320,4445] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,1],[3,1,2,3],[0,1,2,3],[0,0,0,3]]», by decideFin!⟩
