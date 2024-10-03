import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[2,3,0,1],[2,3,1,0],[2,3,0,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[2,3,0,1],[2,3,1,0],[2,3,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[2,3,0,1],[2,3,1,0],[2,3,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[2,3,0,1],[2,3,1,0],[2,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1370,1738,2087,2115,2203] [127,138,151,153,156,159,166,179,194,419,436,466,500,528,575,1035,1299,1315,1336,1353,1405,1426,1428,1444,1481,2050,2078,2182,2227,3862,3887,3915,3925,3935,3952,3962,3972,3989,4006,4023,4040,4275,4307,4606,4615,4645,4689] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[2,3,0,1],[2,3,1,0],[2,3,0,1]]», by decideFin!⟩
