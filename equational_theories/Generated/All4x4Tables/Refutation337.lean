
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,2,1],[3,3,3,3],[1,1,1,1],[0,2,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,1,2,1],[3,3,3,3],[1,1,1,1],[0,2,2,2]]» : Magma (Fin 4) where
  op := finOpTable "[[1,1,2,1],[3,3,3,3],[1,1,1,1],[0,2,2,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,1,2,1],[3,3,3,3],[1,1,1,1],[0,2,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2868] [263, 2035, 2659, 2662, 2669, 2672, 2852, 2855, 2872, 2875, 3258, 3309, 3316, 3319, 3509, 3512, 3519, 3522, 4284, 4599, 4631] :=
    ⟨Fin 4, «All4x4Tables [[1,1,2,1],[3,3,3,3],[1,1,1,1],[0,2,2,2]]», Finite.of_fintype _, by decideFin!⟩
