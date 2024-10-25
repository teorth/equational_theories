
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,2,4,3],[2,3,0,1,4],[3,1,4,0,2],[0,4,3,2,1],[4,2,1,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,2,4,3],[2,3,0,1,4],[3,1,4,0,2],[0,4,3,2,1],[4,2,1,3,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,0,2,4,3],[2,3,0,1,4],[3,1,4,0,2],[0,4,3,2,1],[4,2,1,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,2,4,3],[2,3,0,1,4],[3,1,4,0,2],[0,4,3,2,1],[4,2,1,3,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [474, 2722, 2743] [255, 427, 429, 473, 817, 1036, 1113, 1635, 1848, 1861, 2441, 2669, 2746, 2847, 3112, 3152, 3271, 3346, 3659, 3878, 3924, 4320, 4647, 4658] :=
    ⟨Fin 5, «FinitePoly [[1,0,2,4,3],[2,3,0,1,4],[3,1,4,0,2],[0,4,3,2,1],[4,2,1,3,0]]», Finite.of_fintype _, by decideFin!⟩
