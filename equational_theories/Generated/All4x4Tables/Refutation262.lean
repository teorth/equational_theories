
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,2],[2,0,1],[1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,2],[2,0,1],[1,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[1,1,2],[2,0,1],[1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,2],[2,0,1],[1,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1922, 4157, 4293] [47, 1020, 1629, 1857, 1861, 1894, 2441, 2644, 3050, 3456, 3659, 4068, 4090, 4118, 4165, 4270, 4273, 4320, 4605, 4622, 4656] :=
    ⟨Fin 3, «FinitePoly [[1,1,2],[2,0,1],[1,2,0]]», Finite.of_fintype _, by decideFin!⟩
