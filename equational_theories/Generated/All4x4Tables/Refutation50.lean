
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0],[0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0],[0,0]]» : Magma (Fin 2) where
  op := finOpTable "[[0,0],[0,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0],[0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [41] [47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050] :=
    ⟨Fin 2, «All4x4Tables [[0,0],[0,0]]», Finite.of_fintype _, by decideFin!⟩
