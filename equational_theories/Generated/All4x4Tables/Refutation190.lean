
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,3,3],[1,1,2,2],[1,1,2,2],[0,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,3,3],[1,1,2,2],[1,1,2,2],[0,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,3,3],[1,1,2,2],[1,1,2,2],[0,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,3,3],[1,1,2,2],[1,1,2,2],[0,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3515, 3736, 4402] [3255, 3316, 3461, 3464, 4269, 4435] :=
    ⟨Fin 4, «FinitePoly [[0,3,3,3],[1,1,2,2],[1,1,2,2],[0,3,3,3]]», by decideFin!⟩
