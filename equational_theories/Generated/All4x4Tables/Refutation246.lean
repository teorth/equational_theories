
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,1,3],[3,3,2,3],[0,1,0,0],[0,2,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,1,3],[3,3,2,3],[0,1,0,0],[0,2,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,1,3],[3,3,2,3],[0,1,0,0],[0,2,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,1,3],[3,3,2,3],[0,1,0,0],[0,2,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2665] [4584] :=
    ⟨Fin 4, «FinitePoly [[1,1,1,3],[3,3,2,3],[0,1,0,0],[0,2,2,2]]», by decideFin!⟩
