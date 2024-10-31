
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[2,0,2],[1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[2,0,2],[1,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[2,0,2],[1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[2,0,2],[1,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1843, 1845, 1863, 2462, 2472] [151, 1426, 1629, 1833, 1838, 1847, 1848, 1851, 1858, 2035, 2244, 2247, 2253, 2254, 2257, 2264, 2266, 2444, 2449, 2457, 2460, 2467, 2644, 3050, 3253, 3456, 3664, 3668, 3712, 3862, 4071, 4074, 4118, 4120, 4121, 4127, 4130, 4131, 4269, 4283, 4314, 4380, 4584, 4585, 4598, 4599, 4629] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[2,0,2],[1,1,0]]», Finite.of_fintype _, by decideFin!⟩
