
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1,3],[3,1,2,1],[2,0,2,0],[2,0,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1,3],[3,1,2,1],[2,0,2,0],[2,0,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,1,3],[3,1,2,1],[2,0,2,0],[2,0,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1,3],[3,1,2,1],[2,0,2,0],[2,0,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1482] [151, 1427, 1428, 1429, 1479, 2035, 3456, 3862, 4314, 4606] :=
    ⟨Fin 4, «FinitePoly [[0,1,1,3],[3,1,2,1],[2,0,2,0],[2,0,3,1]]», by decideFin!⟩
