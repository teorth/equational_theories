
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[2,2,1],[0,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,1],[2,2,1],[0,1,2]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,1],[2,2,1],[0,1,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,1],[2,2,1],[0,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1885, 2088] [40, 43, 414, 427, 429, 473, 477, 511, 513, 1682, 1731, 1861, 1934, 2470, 3056, 3079] :=
    ⟨Fin 3, «All4x4Tables [[0,0,1],[2,2,1],[0,1,2]]», Finite.of_fintype _, by decideFin!⟩
