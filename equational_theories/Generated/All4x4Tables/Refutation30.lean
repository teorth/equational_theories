
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,1,1],[2,2,2,2],[0,0,3,3],[1,1,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,1,1],[2,2,2,2],[0,0,3,3],[1,1,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,1,1],[2,2,2,2],[0,0,3,3],[1,1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,1,1],[2,2,2,2],[0,0,3,3],[1,1,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2691, 4314, 4655] [2035, 2647, 2650, 2660, 2853, 2863, 3255, 3256, 3258, 3259, 3261, 3308, 3309, 3315, 3316, 3319, 3456, 3659, 4065, 4269, 4270, 4283, 4284, 4598, 4606, 4656] :=
    ⟨Fin 4, «FinitePoly [[1,1,1,1],[2,2,2,2],[0,0,3,3],[1,1,1,1]]», Finite.of_fintype _, by decideFin!⟩
