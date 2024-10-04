
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,3,3],[1,1,1,0],[1,2,2,2],[0,0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,3,3],[1,1,1,0],[1,2,2,2],[0,0,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,3,3],[1,1,1,0],[1,2,2,2],[0,0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,3,3],[1,1,1,0],[1,2,2,2],[0,0,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1845] [2469] :=
    ⟨Fin 4, «FinitePoly [[2,3,3,3],[1,1,1,0],[1,2,2,2],[0,0,0,1]]», by decideFin!⟩
