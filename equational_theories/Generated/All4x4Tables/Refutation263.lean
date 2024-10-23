
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,2,0],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[0,2,0],[0,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[0,2,0],[0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[0,2,0],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4417, 4430, 4449, 4457] [4270, 4272, 4284, 4290, 4314, 4320, 4343, 4396, 4408, 4433, 4445, 4470, 4472, 4473, 4479, 4480, 4583, 4590, 4598, 4599, 4605, 4606, 4608] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[0,2,0],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
