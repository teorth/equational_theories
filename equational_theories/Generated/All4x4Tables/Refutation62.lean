
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[3,0,3,3],[0,3,0,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,3],[3,0,3,3],[0,3,0,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,3],[3,0,3,3],[0,3,0,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,3],[3,0,3,3],[0,3,0,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3714, 3721, 3748, 3751, 3752, 3759, 3761, 4291, 4293, 4321, 4399, 4406, 4436, 4443, 4629, 4636, 4658] [3253, 3456, 3862, 4065, 4284, 4290, 4314, 4320, 4343, 4396, 4433, 4470, 4480, 4598, 4599, 4605, 4606, 4608] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,3],[3,0,3,3],[0,3,0,3],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
