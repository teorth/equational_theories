
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,4,1],[4,0,2,1,3],[1,4,0,3,2],[2,3,1,0,4],[3,1,4,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,4,1],[4,0,2,1,3],[1,4,0,3,2],[2,3,1,0,4],[3,1,4,2,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,3,4,1],[4,0,2,1,3],[1,4,0,3,2],[2,3,1,0,4],[3,1,4,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,4,1],[4,0,2,1,3],[1,4,0,3,2],[2,3,1,0,4],[3,1,4,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [481, 1496, 2146, 3115, 3161] [614, 817, 1020, 1113, 1223, 1434, 1444, 1451, 1481, 1528, 1629, 1832, 2064, 2238, 2441, 2644, 2847, 3152, 3456, 3862, 4065, 4118, 4275, 4290, 4320, 4380, 4605, 4684] :=
    ⟨Fin 5, «FinitePoly [[0,2,3,4,1],[4,0,2,1,3],[1,4,0,3,2],[2,3,1,0,4],[3,1,4,2,0]]», by decideFin!⟩
