
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,0,1],[3,1,0,1],[3,1,3,1],[0,2,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,0,1],[3,1,0,1],[3,1,3,1],[0,2,0,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,0,1],[3,1,0,1],[3,1,3,1],[0,2,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,0,1],[3,1,0,1],[3,1,3,1],[0,2,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1480] [1482, 2035, 3457, 3462, 3511, 3512, 3521, 3522, 3862, 4268, 4314, 4606] :=
    ⟨Fin 4, «FinitePoly [[0,2,0,1],[3,1,0,1],[3,1,3,1],[0,2,0,2]]», Finite.of_fintype _, by decideFin!⟩
