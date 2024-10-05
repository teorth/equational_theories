
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,3,4],[2,1,0,3,4],[2,4,0,1,3],[2,1,0,3,4],[2,1,0,3,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,0,3,4],[2,1,0,3,4],[2,4,0,1,3],[2,1,0,3,4],[2,1,0,3,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[2,1,0,3,4],[2,1,0,3,4],[2,4,0,1,3],[2,1,0,3,4],[2,1,0,3,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,0,3,4],[2,1,0,3,4],[2,4,0,1,3],[2,1,0,3,4],[2,1,0,3,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [476, 503, 510] [375, 466, 3880] :=
    ⟨Fin 5, «FinitePoly [[2,1,0,3,4],[2,1,0,3,4],[2,4,0,1,3],[2,1,0,3,4],[2,1,0,3,4]]», by decideFin!⟩
