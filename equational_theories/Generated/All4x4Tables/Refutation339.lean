
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,1,1],[3,1,1,1],[3,2,2,2],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,1,1],[3,1,1,1],[3,2,2,2],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,1,1],[3,1,1,1],[3,2,2,2],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,1,1],[3,1,1,1],[3,2,2,2],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [621] [50, 56, 99, 151, 203, 255, 411, 623, 629, 630, 632, 633, 639, 640, 642, 643, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3660, 3661, 3664, 3665, 3667, 3668, 3712, 3714, 3721, 3722, 3724, 3862, 4065, 4268, 4269, 4270, 4283, 4284, 4314, 4380, 4583, 4584, 4585, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[2,0,1,1],[3,1,1,1],[3,2,2,2],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
