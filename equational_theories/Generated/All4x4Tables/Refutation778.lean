
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,4,1],[2,1,2,4,4],[3,1,2,4,1],[4,2,0,3,4],[0,2,1,3,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,1,4,1],[2,1,2,4,4],[3,1,2,4,1],[4,2,0,3,4],[0,2,1,3,4]]» : Magma (Fin 5) where
  op := finOpTable "[[0,2,1,4,1],[2,1,2,4,4],[3,1,2,4,1],[4,2,0,3,4],[0,2,1,3,4]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,1,4,1],[2,1,2,4,4],[3,1,2,4,1],[4,2,0,3,4],[0,2,1,3,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3102] [1238, 2087, 2456, 2530, 2669, 2696, 2862, 2899, 2936, 3065, 3139, 4080] :=
    ⟨Fin 5, «All4x4Tables [[0,2,1,4,1],[2,1,2,4,4],[3,1,2,4,1],[4,2,0,3,4],[0,2,1,3,4]]», Finite.of_fintype _, by decideFin!⟩
