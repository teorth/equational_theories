
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,2,3],[3,2,0,3],[2,0,2,0],[3,3,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,2,2,3],[3,2,0,3],[2,0,2,0],[3,3,0,3]]» : Magma (Fin 4) where
  op := finOpTable "[[2,2,2,3],[3,2,0,3],[2,0,2,0],[3,3,0,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,2,2,3],[3,2,0,3],[2,0,2,0],[3,3,0,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3954] [3253, 3714, 3721, 3725, 3749, 3761, 3915, 3928, 3962, 4290, 4658] :=
    ⟨Fin 4, «All4x4Tables [[2,2,2,3],[3,2,0,3],[2,0,2,0],[3,3,0,3]]», Finite.of_fintype _, by decideFin!⟩
