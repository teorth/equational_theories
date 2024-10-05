
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,2,3],[3,3,3,2],[0,1,0,0],[1,0,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,2,3],[3,3,3,2],[0,1,0,0],[1,0,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,2,3],[3,3,3,2],[0,1,0,0],[1,0,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,2,3],[3,3,3,2],[0,1,0,0],[1,0,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1453] [1454, 2238, 3518, 3519, 3522] :=
    ⟨Fin 4, «FinitePoly [[2,2,2,3],[3,3,3,2],[0,1,0,0],[1,0,1,1]]», by decideFin!⟩
