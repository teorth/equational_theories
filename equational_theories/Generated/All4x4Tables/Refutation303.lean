
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,1,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2337, 2804, 2973] [280, 619, 832, 1035, 1228, 1248, 1478, 1634, 1681, 1691, 1884, 2050, 2124, 2243, 2290, 2493, 2503, 2659, 2706, 2733, 2852, 2872, 2909, 2946, 3055, 3075, 3112, 3149, 3306, 3309, 3353, 3461, 3509, 3512, 3674, 3712, 3877, 3925, 4070, 4090, 4128, 4155, 4284, 4396, 4666] :=
    ⟨Fin 4, «FinitePoly [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,1,3]]», Finite.of_fintype _, by decideFin!⟩
