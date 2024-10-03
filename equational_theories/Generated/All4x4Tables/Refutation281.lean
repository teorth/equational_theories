import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,1,1],[3,0,3,2],[2,2,2,2],[2,0,0,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,1,1],[3,0,3,2],[2,2,2,2],[2,0,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,1,1],[3,0,3,2],[2,2,2,2],[2,0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,1,1],[3,0,3,2],[2,2,2,2],[2,0,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1427,1428,1431,1638] [151,152,153,156,1444,1647,1832,1840,1858,3253,3261,3306,3456,3459,4065,4118,4121,4128,4131,4599] :=
    ⟨Fin 4, «FinitePoly [[3,2,1,1],[3,0,3,2],[2,2,2,2],[2,0,0,1]]», by decideFin!⟩
