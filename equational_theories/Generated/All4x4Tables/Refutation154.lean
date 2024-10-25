
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,1,2],[0,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[0,1,2],[0,2,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[0,1,2],[0,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[0,1,2],[0,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1109, 1780, 1887] [1028, 1036, 1038, 1049, 1113, 1635, 1848, 1861, 2447, 2470, 2534, 3878, 3924, 4647] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[0,1,2],[0,2,1]]», Finite.of_fintype _, by decideFin!⟩
