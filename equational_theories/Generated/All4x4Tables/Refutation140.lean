import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[1,0,2,3],[2,1,0,3],[3,1,2,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[1,0,2,3],[2,1,0,3],[3,1,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[1,0,2,3],[2,1,0,3],[3,1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[1,0,2,3],[2,1,0,3],[3,1,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [676,703,731,872,981,1523,1543,2038,2090,2132,2293,2402,2964] [632,639,669,765,778,825,879,934,968,1442,1444,1451,1488,1577,1590,2051,2256,2389,2449,2503,2558,2592,2669,2808,2998,3075,3112,3201,3214,3462,3474,3497,3511,3868,3880,3903,3917,3997,4073,4083,4146,4158,4200,4320,4362,4635,4677] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[1,0,2,3],[2,1,0,3],[3,1,2,0]]», by decideFin!⟩
