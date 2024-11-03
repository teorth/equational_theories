
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[0,0,1],[2,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[0,0,1],[2,1,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[0,0,1],[2,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[0,0,1],[2,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4423] [4270, 4272, 4275, 4276, 4284, 4290, 4293, 4343, 4358, 4396, 4406, 4435, 4445, 4470, 4472, 4480, 4482, 4583, 4591, 4598, 4608, 4636, 4647] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[0,0,1],[2,1,1]]», Finite.of_fintype _, by decideFin!⟩
