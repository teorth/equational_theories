
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,0,0],[4,1,4,4,1],[2,2,2,2,2],[3,3,3,3,3],[4,4,4,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,0,0],[4,1,4,4,1],[2,2,2,2,2],[3,3,3,3,3],[4,4,4,4,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,3,0,0],[4,1,4,4,1],[2,2,2,2,2],[3,3,3,3,3],[4,4,4,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,0,0],[4,1,4,4,1],[2,2,2,2,2],[3,3,3,3,3],[4,4,4,4,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [418] [50, 419, 420, 623, 820, 823, 825, 826, 1021, 1026, 1029, 1224, 1226, 1232, 1429, 1630, 1632, 1833, 1837, 1838, 2036, 2246, 2443, 2449, 2646, 2852, 3256, 3457, 3459, 3660, 3864, 3918, 4268] :=
    ⟨Fin 5, «FinitePoly [[0,2,3,0,0],[4,1,4,4,1],[2,2,2,2,2],[3,3,3,3,3],[4,4,4,4,4]]», Finite.of_fintype _, by decideFin!⟩
