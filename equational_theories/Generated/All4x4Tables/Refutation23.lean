import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[3,0,1,2],[3,0,2,1],[2,0,3,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[3,0,1,2],[3,0,2,1],[2,0,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[3,0,1,2],[3,0,2,1],[2,0,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[3,0,1,2],[3,0,2,1],[2,0,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [440,1525] [47,55,72,359,375,614,642,669,676,703,817,820,823,833,835,842,845,846,850,858,882,909,916,1023,1036,1049,1053,1064,1226,1229,1239,1252,1256,1264,1267,1434,1444,1481,1835,1861,1865,3256,3315,3323,3665,3721,3729,3865,3870,3880,3887,3915,3928,3943,3955,3962,3997,4023,4068,4071,4118,4270,4275,4307,4341,4598,4673] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[3,0,1,2],[3,0,2,1],[2,0,3,1]]», by decideFin!⟩
