
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,3,0,3],[3,3,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,3,0,3],[3,3,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,3,0,3],[3,3,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,3,0,3],[3,3,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3277, 3476, 3479, 3889, 3899, 4079, 4430] [3458, 3482, 3867, 3881, 4269, 4273, 4283, 4291, 4314, 4321, 4398, 4406, 4435, 4436, 4442, 4443, 4606, 4629, 4631, 4635, 4636, 4647] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,3,0,3],[3,3,3,3],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
