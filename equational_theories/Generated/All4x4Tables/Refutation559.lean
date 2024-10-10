
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,2,3,3],[0,3,3,3,0],[4,3,3,3,4],[4,2,1,3,0],[3,1,1,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,2,3,3],[0,3,3,3,0],[4,3,3,3,4],[4,2,1,3,0],[3,1,1,3,3]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[3,2,2,3,3],[0,3,3,3,0],[4,3,3,3,4],[4,2,1,3,0],[3,1,1,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,2,3,3],[0,3,3,3,0],[4,3,3,3,4],[4,2,1,3,0],[3,1,1,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1724] [1644, 1647, 1657, 4118, 4128, 4155, 4165] :=
    ⟨Fin 5, «FinitePoly [[3,2,2,3,3],[0,3,3,3,0],[4,3,3,3,4],[4,2,1,3,0],[3,1,1,3,3]]», by decideFin!⟩
