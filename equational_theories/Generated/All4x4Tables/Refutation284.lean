
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[2,2,0],[0,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,2],[2,2,0],[0,0,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,2],[2,2,0],[0,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,2],[2,2,0],[0,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3388, 3541, 3837, 4428] [307, 3255, 3256, 3258, 3259, 3262, 3309, 3316, 3459, 3511, 3521, 3662, 3665, 3668, 3725, 3862, 4065, 4269, 4270, 4272, 4284, 4291, 4314, 4435, 4442, 4470, 4473, 4480] :=
    ⟨Fin 3, «FinitePoly [[0,0,2],[2,2,0],[0,0,2]]», Finite.of_fintype _, by decideFin!⟩
