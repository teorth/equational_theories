
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,1],[2,2,2],[0,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,1],[2,2,2],[0,0,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[1,1,1],[2,2,2],[0,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,1],[2,2,2],[0,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2048] [47, 99, 151, 203, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2088, 2124, 2128, 2238, 2441, 2697, 2699, 2710, 2744, 2746, 2900, 2902, 2909, 2940, 2947, 2949, 3050, 3271, 3278, 3342, 3346, 3353, 3472, 3474, 3481, 3545, 3549, 3558, 3659, 3862, 4065, 4273, 4275, 4290, 4320, 4380, 4588, 4590, 4605, 4635] :=
    ⟨Fin 3, «FinitePoly [[1,1,1],[2,2,2],[0,0,0]]», Finite.of_fintype _, by decideFin!⟩
