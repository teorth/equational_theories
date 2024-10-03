import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,3],[0,1,2,3],[3,1,2,0],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,3],[0,1,2,3],[3,1,2,0],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,1,3],[0,1,2,3],[3,1,2,0],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,3],[0,1,2,3],[3,1,2,0],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [65,72,679,713,723,909,916,947,1370,1491,1506,1518,2063,2203] [117,138,159,194,385,395,632,653,669,676,690,825,860,879,882,960,1278,1299,1315,1336,1353,1387,1405,1444,1451,1481,1560,1586,2043,2078,2100,2115,2152,2182,2227,3880,3925,3935,3952,3955,3972,3989,3997,4006,4040,4073,4083,4128,4131,4138,4146,4158,4165,4175,4200,4209,4226,4243,4606,4615,4635,4645,4677,4689] :=
    ⟨Fin 4, «FinitePoly [[0,2,1,3],[0,1,2,3],[3,1,2,0],[0,1,2,3]]», by decideFin!⟩
