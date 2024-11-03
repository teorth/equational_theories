
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[0,0,2],[0,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,2],[0,0,2],[0,2,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,2],[0,0,2],[0,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,2],[0,0,2],[0,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3583, 3587, 3600] [3255, 3261, 3271, 3281, 3309, 3319, 3346, 3458, 3461, 3464, 3474, 3481, 3484, 3522, 3661, 3667, 3677, 3687, 3725, 3752, 3864, 3867, 3870, 3880, 3887, 3890, 3928, 4067, 4070, 4073, 4080, 4083, 4090, 4093, 4269, 4275, 4284, 4320, 4470, 4473, 4480, 4584, 4587, 4590, 4677] :=
    ⟨Fin 3, «FinitePoly [[0,0,2],[0,0,2],[0,2,2]]», Finite.of_fintype _, by decideFin!⟩
