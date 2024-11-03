
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,0,2],[0,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[0,0,2],[0,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[0,0,2],[0,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[0,0,2],[0,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [385, 3479, 3483, 3679, 3696, 3882, 3885, 4331, 4447, 4457, 4484, 4487] [3462, 3474, 3667, 3675, 3864, 3888, 3925, 4071, 4083, 4131, 4155, 4291, 4396, 4398, 4409, 4435, 4443, 4472, 4480, 4598, 4606, 4629, 4631, 4635, 4636, 4647] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[0,0,2],[0,1,0]]», Finite.of_fintype _, by decideFin!⟩
