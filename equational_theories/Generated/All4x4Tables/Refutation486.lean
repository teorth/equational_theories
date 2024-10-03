import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2592,3112,3201] [23,31,411,513,1629,1637,1718,1731,1746,2238,2246,2256,2263,2293,2300,2327,2340,2355,2389,2402,2449,2466,2496,2530,2558,2605,2644,2652,2662,2669,2699,2706,2733,2746,2761,2795,2808,2847,2855,2865,2872,2902,2909,2936,2949,2964,2998,3011,3058,3075,3105,3139,3167,3214,3456,3464,3509,3522,3537,3659,3684,3712,3759,3820,4065,4090,4118,4165,4226,4320,4590,4622] :=
    ⟨Fin 5, «FinitePoly [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]», by decideFin!⟩
