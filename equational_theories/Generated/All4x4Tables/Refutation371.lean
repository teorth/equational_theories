
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4444] [4270, 4272, 4314, 4320, 4343, 4470, 4472, 4473, 4479, 4480, 4482] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
