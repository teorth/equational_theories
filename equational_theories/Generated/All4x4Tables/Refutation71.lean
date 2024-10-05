
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,0,1],[3,2,1,0],[0,1,2,3],[2,0,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,0,1],[3,2,1,0],[0,1,2,3],[2,0,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,0,1],[3,2,1,0],[0,1,2,3],[2,0,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,0,1],[3,2,1,0],[0,1,2,3],[2,0,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2737, 3152] [1898, 1925, 2101, 2238, 2441, 2699, 2710, 2744, 2940, 2947, 3068, 3116, 3150, 3306, 4283, 4290, 4396, 4398, 4405, 4433, 4435, 4442, 4480, 4677, 4679] :=
    ⟨Fin 4, «FinitePoly [[1,3,0,1],[3,2,1,0],[0,1,2,3],[2,0,3,2]]», by decideFin!⟩
