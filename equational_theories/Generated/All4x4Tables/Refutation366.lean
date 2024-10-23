
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,2,3],[3,0,3,2],[0,1,2,3],[0,1,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,2,3],[3,0,3,2],[0,1,2,3],[0,1,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,2,3],[3,0,3,2],[0,1,2,3],[0,1,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,2,3],[3,0,3,2],[0,1,2,3],[0,1,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2484, 2778] [231, 2240, 2290, 2303, 2330, 2506, 2543, 2672, 4118, 4320] :=
    ⟨Fin 4, «FinitePoly [[2,0,2,3],[3,0,3,2],[0,1,2,3],[0,1,2,2]]», Finite.of_fintype _, by decideFin!⟩
