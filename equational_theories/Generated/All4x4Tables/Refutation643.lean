
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[4,4,4,4,4],[2,4,2,3,4],[3,1,4,3,4],[4,1,2,4,4],[0,1,2,3,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[4,4,4,4,4],[2,4,2,3,4],[3,1,4,3,4],[4,1,2,4,4],[0,1,2,3,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[4,4,4,4,4],[2,4,2,3,4],[3,1,4,3,4],[4,1,2,4,4],[0,1,2,3,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[4,4,4,4,4],[2,4,2,3,4],[3,1,4,3,4],[4,1,2,4,4],[0,1,2,3,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3145] [2530, 2712, 3078, 3105] :=
    ⟨Fin 5, «FinitePoly [[4,4,4,4,4],[2,4,2,3,4],[3,1,4,3,4],[4,1,2,4,4],[0,1,2,3,4]]», by decideFin!⟩
