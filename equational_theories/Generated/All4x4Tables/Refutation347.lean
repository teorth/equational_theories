import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [117,1848,1876,2100,2939] [3,5,8,10,13,16,19,23,25,26,28,31,34,39,45,411,1426,1429,1432,1434,1442,1444,1451,1455,1459,1467,1470,1629,1632,1635,1637,1645,1647,1654,1658,1662,1670,1673,1835,1838,1850,1857,1865,1873,2043,2124,2127,2134,2238,2241,2244,2246,2254,2256,2263,2267,2271,2279,2282,2441,2444,2447,2449,2457,2459,2466,2470,2474,2482,2485,2644,2743,3253,3256,3259,3261,3306,3308,3315,3319,3323,3334,3456,3462,3511,4065,4270,4341,4598,4673] :=
    ⟨Fin 4, «FinitePoly [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]», by decideFin!⟩
