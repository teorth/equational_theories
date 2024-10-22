
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,3,3],[2,2,2,2],[1,1,1,1],[0,0,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,3,3],[2,2,2,2],[1,1,1,1],[0,0,0,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,3,3],[2,2,2,2],[1,1,1,1],[0,0,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,3,3],[2,2,2,2],[1,1,1,1],[0,0,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1845, 1863, 2462, 2472, 4128] [1426, 1629, 1833, 1838, 1847, 1848, 1851, 1858, 2244, 2247, 2253, 2254, 2264, 2266, 2444, 2449, 2457, 2460, 2467, 2644, 3050, 3253, 3456, 3659, 3862, 4071, 4073, 4074, 4118, 4120, 4121, 4127, 4130, 4131, 4269, 4283, 4314, 4584, 4599, 4605, 4608, 4629, 4658] :=
    ⟨Fin 4, «FinitePoly [[2,3,3,3],[2,2,2,2],[1,1,1,1],[0,0,0,2]]», Finite.of_fintype _, by decideFin!⟩
