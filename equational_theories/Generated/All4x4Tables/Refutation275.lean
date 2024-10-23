
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,0,0],[1,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[0,0,0],[1,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[0,0,0],[1,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[0,0,0],[1,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3470, 4387] [307, 3255, 3256, 3660, 3661, 3662, 3665, 3667, 3668, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4283, 4284, 4293, 4320, 4343, 4396, 4398, 4433, 4435, 4436, 4442, 4443, 4445, 4470, 4472, 4473, 4479, 4480, 4482] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[0,0,0],[1,0,1]]», Finite.of_fintype _, by decideFin!⟩
