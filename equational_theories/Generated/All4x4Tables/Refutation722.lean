
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1,3,4,5],[5,1,2,4,5,5],[3,1,2,5,5,0],[0,1,1,3,4,5],[5,2,1,3,4,5],[0,2,1,3,4,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,1,1,3,4,5],[5,1,2,4,5,5],[3,1,2,5,5,0],[0,1,1,3,4,5],[5,2,1,3,4,5],[0,2,1,3,4,5]]» : Magma (Fin 6) where
  op := finOpTable "[[0,1,1,3,4,5],[5,1,2,4,5,5],[3,1,2,5,5,0],[0,1,1,3,4,5],[5,2,1,3,4,5],[0,2,1,3,4,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,1,1,3,4,5],[5,1,2,4,5,5],[3,1,2,5,5,0],[0,1,1,3,4,5],[5,2,1,3,4,5],[0,2,1,3,4,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2381] [323, 1055, 1958, 2364, 2584, 2669, 3897] :=
    ⟨Fin 6, «All4x4Tables [[0,1,1,3,4,5],[5,1,2,4,5,5],[3,1,2,5,5,0],[0,1,1,3,4,5],[5,2,1,3,4,5],[0,2,1,3,4,5]]», Finite.of_fintype _, by decideFin!⟩
