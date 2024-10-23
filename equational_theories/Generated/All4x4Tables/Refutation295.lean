
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[0,0,0],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[0,0,0],[0,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[0,0,0],[0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[0,0,0],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3909, 4528] [359, 3253, 3456, 3659, 4070, 4090, 4396, 4398, 4406, 4408, 4433, 4435, 4443, 4445, 4470, 4472, 4480, 4482, 4583, 4584, 4588, 4590, 4598, 4608, 4636] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[0,0,0],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
