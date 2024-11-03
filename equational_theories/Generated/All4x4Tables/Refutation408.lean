
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [162, 1447, 3089] [3058, 3075, 4073, 4121, 4599] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]», Finite.of_fintype _, by decideFin!⟩
