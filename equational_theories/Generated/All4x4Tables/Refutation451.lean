
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,1,3],[3,3,3,3],[1,1,0,3],[0,1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,2,1,3],[3,3,3,3],[1,1,0,3],[0,1,2,0]]» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,3],[3,3,3,3],[1,1,0,3],[0,1,2,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,2,1,3],[3,3,3,3],[1,1,0,3],[0,1,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3052] [2644, 3058, 3065, 3068, 3253, 3456, 3659, 4269, 4270, 4314, 4631] :=
    ⟨Fin 4, «All4x4Tables [[2,2,1,3],[3,3,3,3],[1,1,0,3],[0,1,2,0]]», Finite.of_fintype _, by decideFin!⟩
