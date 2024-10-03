import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,3,3],[3,2,2,2],[1,1,1,0],[0,0,0,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,3,3],[3,2,2,2],[1,1,1,0],[0,0,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,3,3],[3,2,2,2],[1,1,1,0],[0,0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,3,3],[3,2,2,2],[1,1,1,0],[0,0,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1429,1453,1454,1456,1841,1845,2264,2270,2444] [23,24,25,26,27,38,42,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,204,206,207,208,212,307,326,1428,1834,1840,1843,1860,1863,2256,2443,2456,2457,2459,2462,2472,3053,3058,3066,3075,3083,3094,3456,3459,3518,3521,3522,3526,4065,4066,4067,4068,4069,4070,4128,4314,4583,4585,4597,4598,4656,4673] :=
    ⟨Fin 4, «FinitePoly [[2,3,3,3],[3,2,2,2],[1,1,1,0],[0,0,0,1]]», by decideFin!⟩
