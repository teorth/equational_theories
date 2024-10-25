
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,3,1],[3,2,1,0],[0,1,2,3],[1,3,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,3,1],[3,2,1,0],[0,1,2,3],[1,3,0,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,3,1],[3,2,1,0],[0,1,2,3],[1,3,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,3,1],[3,2,1,0],[0,1,2,3],[1,3,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [414, 417, 427, 464] [99, 359, 413, 426, 429, 436, 440, 466, 614, 817, 1036, 1049, 1075, 1223, 1426, 2035, 2238, 2447, 2847, 3253, 3545, 3721, 3725, 3862, 4167, 4283, 4380, 4635] :=
    ⟨Fin 4, «FinitePoly [[2,0,3,1],[3,2,1,0],[0,1,2,3],[1,3,0,2]]», Finite.of_fintype _, by decideFin!⟩
