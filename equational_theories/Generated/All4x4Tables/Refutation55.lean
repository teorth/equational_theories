
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,0,3],[3,0,2,0],[0,3,3,2],[3,1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,0,3],[3,0,2,0],[0,3,3,2],[3,1,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,0,3],[3,0,2,0],[0,3,3,2],[3,1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,0,3],[3,0,2,0],[0,3,3,2],[3,1,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2540, 3272, 4343] [47, 307, 1629, 1832, 2449, 2533, 3050, 3259, 3261, 3456, 3659, 4073, 4118, 4131, 4273] :=
    ⟨Fin 4, «FinitePoly [[2,0,0,3],[3,0,2,0],[0,3,3,2],[3,1,2,0]]», Finite.of_fintype _, by decideFin!⟩
