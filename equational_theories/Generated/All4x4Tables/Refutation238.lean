
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,0,0],[1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[0,0,0],[1,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[0,0,0],[1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[0,0,0],[1,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [366, 4271] [3253, 3456, 3712, 3714, 3721, 3725, 3748, 3752, 3759, 3761, 3915, 3928, 4131, 4272, 4273, 4275, 4276, 4290, 4291, 4293, 4320, 4321, 4343, 4380] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[0,0,0],[1,1,0]]», Finite.of_fintype _, by decideFin!⟩
