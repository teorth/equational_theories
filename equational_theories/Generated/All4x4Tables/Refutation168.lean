
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[1,1,0],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[1,1,0],[0,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[1,1,0],[0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[1,1,0],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3947, 4143, 4521] [359, 3253, 3456, 3665, 3667, 3712, 3714, 3865, 3868, 3917, 4067, 4070, 4121, 4128, 4396, 4398, 4433, 4435, 4470, 4472, 4583, 4599, 4629, 4631] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[1,1,0],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
