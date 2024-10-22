
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,0,3],[3,3,3,0],[2,2,2,2],[1,0,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,0,3],[3,3,3,0],[2,2,2,2],[1,0,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,0,3],[3,3,3,0],[2,2,2,2],[1,0,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,0,3],[3,3,3,0],[2,2,2,2],[1,0,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1435, 1635, 3262, 3465, 3521] [2441, 3050, 3258, 3259, 3457, 3459, 3462, 3511, 3518, 3862, 4065, 4283, 4284, 4398, 4435, 4472, 4599] :=
    ⟨Fin 4, «FinitePoly [[0,1,0,3],[3,3,3,0],[2,2,2,2],[1,0,1,1]]», Finite.of_fintype _, by decideFin!⟩
