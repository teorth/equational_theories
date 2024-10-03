import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,1],[0,1,3,2],[0,1,2,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,1],[0,1,3,2],[0,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,1],[0,1,3,2],[0,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,1],[0,1,3,2],[0,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [270,2584,2804,2973,3102,3176,4192,4209] [28,104,166,208,218,260,280,290,333,364,619,832,1025,1035,1228,1248,1258,1478,1634,1681,1701,1847,1884,2050,2124,2161,2243,2253,2290,2337,2493,2530,2567,2659,2706,2733,2770,2787,2852,2872,2882,2909,2919,2946,2956,2990,3007,3024,3055,3068,3075,3085,3112,3122,3149,3159,3193,3210,3227,3461,3533,3674,3867,3877,3897,4070,4090,4100,4269,4316,4385,4587,4666] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,1],[0,1,3,2],[0,1,2,3],[0,1,2,3]]», by decideFin!⟩
