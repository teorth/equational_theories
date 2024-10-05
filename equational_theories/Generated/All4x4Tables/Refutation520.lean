
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,1,6,4,5],[1,4,5,2,0,3,6],[2,3,6,4,1,5,0],[3,6,1,5,4,0,2],[4,5,0,3,2,6,1],[5,0,2,6,3,1,4],[6,1,4,0,5,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,1,6,4,5],[1,4,5,2,0,3,6],[2,3,6,4,1,5,0],[3,6,1,5,4,0,2],[4,5,0,3,2,6,1],[5,0,2,6,3,1,4],[6,1,4,0,5,2,3]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[0,2,3,1,6,4,5],[1,4,5,2,0,3,6],[2,3,6,4,1,5,0],[3,6,1,5,4,0,2],[4,5,0,3,2,6,1],[5,0,2,6,3,1,4],[6,1,4,0,5,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,1,6,4,5],[1,4,5,2,0,3,6],[2,3,6,4,1,5,0],[3,6,1,5,4,0,2],[4,5,0,3,2,6,1],[5,0,2,6,3,1,4],[6,1,4,0,5,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1313, 1315, 1322] [99, 151, 411, 1020, 1238, 1248, 1278, 1288, 2035, 3659, 3862, 4065, 4275, 4320, 4321, 4380, 4605, 4606, 4635, 4636, 4666] :=
    ⟨Fin 7, «FinitePoly [[0,2,3,1,6,4,5],[1,4,5,2,0,3,6],[2,3,6,4,1,5,0],[3,6,1,5,4,0,2],[4,5,0,3,2,6,1],[5,0,2,6,3,1,4],[6,1,4,0,5,2,3]]», by decideFin!⟩
