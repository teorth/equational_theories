
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,4,4,0,2],[2,5,1,1,5,2],[3,0,1,1,0,3],[2,5,4,4,5,2],[3,0,4,4,0,3],[3,5,1,1,5,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,4,4,0,2],[2,5,1,1,5,2],[3,0,1,1,0,3],[2,5,4,4,5,2],[3,0,4,4,0,3],[3,5,1,1,5,3]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[2,0,4,4,0,2],[2,5,1,1,5,2],[3,0,1,1,0,3],[2,5,4,4,5,2],[3,0,4,4,0,3],[3,5,1,1,5,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,4,4,0,2],[2,5,1,1,5,2],[3,0,1,1,0,3],[2,5,4,4,5,2],[3,0,4,4,0,3],[3,5,1,1,5,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1465] [4070, 4073, 4118, 4121, 4599, 4631] :=
    ⟨Fin 6, «FinitePoly [[2,0,4,4,0,2],[2,5,1,1,5,2],[3,0,1,1,0,3],[2,5,4,4,5,2],[3,0,4,4,0,3],[3,5,1,1,5,3]]», by decideFin!⟩
