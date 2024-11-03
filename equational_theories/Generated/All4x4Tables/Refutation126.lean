
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[1,0,0],[2,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[1,0,0],[2,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[1,0,0],[2,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[1,0,0],[2,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1056] [99, 359, 413, 437, 843, 1039, 1229, 1231, 1239, 1241, 1242, 1249, 1251, 3255, 3316, 3724, 3925, 4598] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[1,0,0],[2,1,0]]», Finite.of_fintype _, by decideFin!⟩
