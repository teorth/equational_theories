import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,3,3],[3,2,2,2],[0,3,0,0],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,3,3],[3,2,2,2],[0,3,0,0],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,3,3],[3,2,2,2],[0,3,0,0],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,3,3],[3,2,2,2],[0,3,0,0],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2902,2912,2949] [3,5,8,10,13,16,19,23,25,28,31,34,39,45,47,49,52,55,58,62,65,68,72,75,78,82,86,90,94,99,101,104,107,110,114,117,120,124,127,130,134,138,142,146,151,153,156,159,162,166,169,172,176,179,182,186,190,194,198,203,205,208,211,214,218,221,224,228,231,234,238,242,246,250,411,513,614,716,817,919,1020,1122,1223,1325,1426,1528,1629,1637,1718,1731,1746,1832,1934,2035,2137,2238,2246,2256,2263,2293,2300,2327,2340,2355,2389,2402,2441,2449,2459,2466,2496,2503,2530,2543,2558,2592,2605,2909,2936,3050,3058,3075,3112,3152,3456,3522,4065,4118,4320,4362,4380,4396,4435,4442,4473,4480,4512,4525,4635,4677] :=
    ⟨Fin 4, «FinitePoly [[1,1,3,3],[3,2,2,2],[0,3,0,0],[0,1,2,3]]», by decideFin!⟩
