
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,0,1,0],[1,3,1,5,5,1],[1,2,2,5,1,2],[5,3,3,0,0,3],[2,2,4,3,0,4],[5,4,5,0,5,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,0,0,1,0],[1,3,1,5,5,1],[1,2,2,5,1,2],[5,3,3,0,0,3],[2,2,4,3,0,4],[5,4,5,0,5,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,2,0,0,1,0],[1,3,1,5,5,1],[1,2,2,5,1,2],[5,3,3,0,0,3],[2,2,4,3,0,4],[5,4,5,0,5,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,0,0,1,0],[1,3,1,5,5,1],[1,2,2,5,1,2],[5,3,3,0,0,3],[2,2,4,3,0,4],[5,4,5,0,5,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [646] [99, 151, 203, 255, 411, 615, 619, 620, 622, 623, 629, 630, 632, 633, 639, 642, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4283, 4284, 4314, 4380, 4583, 4584, 4585, 4598, 4599, 4629] :=
    ⟨Fin 6, «FinitePoly [[1,2,0,0,1,0],[1,3,1,5,5,1],[1,2,2,5,1,2],[5,3,3,0,0,3],[2,2,4,3,0,4],[5,4,5,0,5,5]]», Finite.of_fintype _, by decideFin!⟩
