
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,2,1],[3,0,2,2],[2,3,1,3],[0,0,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,2,1],[3,0,2,2],[2,3,1,3],[0,0,1,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,2,1],[3,0,2,2],[2,3,1,3],[0,0,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,2,1],[3,0,2,2],[2,3,1,3],[0,0,1,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1432, 1635] [1832, 2238, 3253] :=
    ⟨Fin 4, «FinitePoly [[3,1,2,1],[3,0,2,2],[2,3,1,3],[0,0,1,2]]», by decideFin!⟩
