
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,0,1],[3,1,1,2],[1,2,2,2],[2,2,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,0,1],[3,1,1,2],[1,2,2,2],[2,2,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,0,1],[3,1,1,2],[1,2,2,2],[2,2,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,0,1],[3,1,1,2],[1,2,2,2],[2,2,3,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [818, 836, 1242] [1020, 1224, 1238, 1239, 1241, 1248, 1249, 1251, 1252, 3253, 4065, 4591, 4598] :=
    ⟨Fin 4, «FinitePoly [[3,0,0,1],[3,1,1,2],[1,2,2,2],[2,2,3,2]]», Finite.of_fintype _, by decideFin!⟩
