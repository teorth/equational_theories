
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[2,0,1],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[2,0,1],[0,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[2,0,1],[0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[2,0,1],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1484, 3883] [47, 307, 3255, 3268, 3271, 3278, 3281, 3326, 3334, 3343, 3346, 3458, 3461, 3464, 3474, 3481, 3484, 3509, 3512, 3519, 3522, 3659, 3867, 3887, 3915, 3925, 3928, 3952, 3962, 4067, 4073, 4083, 4093, 4118, 4121, 4128, 4131, 4155, 4158, 4165, 4269, 4272, 4275, 4284, 4291, 4320, 4380, 4584, 4599, 4635] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[2,0,1],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
