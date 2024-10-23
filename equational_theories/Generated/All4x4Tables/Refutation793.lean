
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,2,0,0],[4,1,1,4,1],[2,4,2,2,2],[4,3,4,3,3],[4,4,4,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,2,0,0],[4,1,1,4,1],[2,4,2,2,2],[4,3,4,3,3],[4,4,4,4,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[2,3,2,0,0],[4,1,1,4,1],[2,4,2,2,2],[4,3,4,3,3],[4,4,4,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,2,0,0],[4,1,1,4,1],[2,4,2,2,2],[4,3,4,3,3],[4,4,4,4,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3321] [3256, 3306, 3316, 3319, 4269, 4270, 4314, 4583, 4631] :=
    ⟨Fin 5, «FinitePoly [[2,3,2,0,0],[4,1,1,4,1],[2,4,2,2,2],[4,3,4,3,3],[4,4,4,4,4]]», Finite.of_fintype _, by decideFin!⟩
