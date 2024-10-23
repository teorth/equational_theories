
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,2,3],[3,3,2,3],[0,3,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,2,3],[3,3,2,3],[0,3,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,2,3],[3,3,2,3],[0,3,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,2,3],[3,3,2,3],[0,3,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [372, 3479, 3483, 3679, 3696, 3885] [3462, 3467, 3474, 3667, 3675, 3864, 3868, 3880, 3888, 4071, 4076, 4083, 4268, 4269, 4284, 4314, 4598, 4606, 4629, 4631, 4635, 4684] :=
    ⟨Fin 4, «FinitePoly [[3,2,2,3],[3,3,2,3],[0,3,3,3],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
