
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]» : Magma (Fin 4) where
  op := finOpTable "[[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2878] [255, 2035, 2644, 2855, 2865, 3253, 3456, 4269, 4284, 4599, 4631] :=
    ⟨Fin 4, «All4x4Tables [[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]», Finite.of_fintype _, by decideFin!⟩
