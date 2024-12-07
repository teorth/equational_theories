
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]» : Magma (Fin 4) where
  op := finOpTable "[[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2089] [3456, 3877, 3880, 3915, 3918, 3952, 3955, 4314, 4606, 4666] :=
    ⟨Fin 4, «All4x4Tables [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]», Finite.of_fintype _, by decideFin!⟩
