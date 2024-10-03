import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,2,3],[1,0,2,3],[0,1,3,2],[1,0,3,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,2,3],[1,0,2,3],[0,1,3,2],[1,0,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,2,3],[1,0,2,3],[0,1,3,2],[1,0,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,2,3],[1,0,2,3],[0,1,3,2],[1,0,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1353] [127,138,179,194,1288,1299,1325,1336,1370,1387,1405,2063,2078,2137,2152,2182,2203,2227,3925,3935,3952,3972,3989,4006,4040,4606,4615,4645,4689] :=
    ⟨Fin 4, «FinitePoly [[1,0,2,3],[1,0,2,3],[0,1,3,2],[1,0,3,2]]», by decideFin!⟩
