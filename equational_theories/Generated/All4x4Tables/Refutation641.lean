
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,2,3,3],[2,1,2,3,3],[3,4,2,3,4],[0,4,0,3,4],[3,1,1,1,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,2,3,3],[2,1,2,3,3],[3,4,2,3,4],[0,4,0,3,4],[3,1,1,1,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,2,3,3],[2,1,2,3,3],[3,4,2,3,4],[0,4,0,3,4],[3,1,1,1,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,2,3,3],[2,1,2,3,3],[3,4,2,3,4],[0,4,0,3,4],[3,1,1,1,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3122] [2909, 2936, 4155] :=
    ⟨Fin 5, «FinitePoly [[0,2,2,3,3],[2,1,2,3,3],[3,4,2,3,4],[0,4,0,3,4],[3,1,1,1,4]]», by decideFin!⟩
