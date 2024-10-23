
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[0,2,1],[2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1],[0,2,1],[2,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,2,1],[0,2,1],[2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1],[0,2,1],[2,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1975, 3901, 3972] [1837, 1857, 2050, 2087, 2124, 3864, 3877, 3887, 3915, 3925, 4067, 4083, 4269, 4284, 4666] :=
    ⟨Fin 3, «FinitePoly [[0,2,1],[0,2,1],[2,0,1]]», Finite.of_fintype _, by decideFin!⟩
