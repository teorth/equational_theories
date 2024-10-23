
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,2,3],[3,0,3,0],[0,1,2,3],[0,2,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,2,3],[3,0,3,0],[0,1,2,3],[0,2,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,2,3],[3,0,3,0],[0,1,2,3],[0,2,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,2,3],[3,0,3,0],[0,1,2,3],[0,2,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2919] [307, 2035, 2644, 3258, 3268, 3278, 3309, 3316, 3319, 3456, 3664, 3674, 3749, 4272, 4284, 4320, 4606] :=
    ⟨Fin 4, «FinitePoly [[0,2,2,3],[3,0,3,0],[0,1,2,3],[0,2,2,3]]», Finite.of_fintype _, by decideFin!⟩
