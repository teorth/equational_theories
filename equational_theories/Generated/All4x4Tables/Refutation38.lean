
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,6,5,3,4,1],[6,1,2,1,1,5,1],[3,2,2,2,6,4,5],[4,1,2,3,3,5,1],[5,1,5,3,4,4,6],[3,5,6,5,4,5,5],[2,1,4,1,6,5,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,6,5,3,4,1],[6,1,2,1,1,5,1],[3,2,2,2,6,4,5],[4,1,2,3,3,5,1],[5,1,5,3,4,4,6],[3,5,6,5,4,5,5],[2,1,4,1,6,5,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,6,5,3,4,1],[6,1,2,1,1,5,1],[3,2,2,2,6,4,5],[4,1,2,3,3,5,1],[5,1,5,3,4,4,6],[3,5,6,5,4,5,5],[2,1,4,1,6,5,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,6,5,3,4,1],[6,1,2,1,1,5,1],[3,2,2,2,6,4,5],[4,1,2,3,3,5,1],[5,1,5,3,4,4,6],[3,5,6,5,4,5,5],[2,1,4,1,6,5,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3555] [3862, 4065, 4272, 4283, 4284, 4290, 4291, 4314, 4320, 4343, 4380, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636] :=
    ⟨Fin 7, «FinitePoly [[1,2,6,5,3,4,1],[6,1,2,1,1,5,1],[3,2,2,2,6,4,5],[4,1,2,3,3,5,1],[5,1,5,3,4,4,6],[3,5,6,5,4,5,5],[2,1,4,1,6,5,6]]», Finite.of_fintype _, by decideFin!⟩
