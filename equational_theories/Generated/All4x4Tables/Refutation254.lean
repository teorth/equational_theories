
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[2,2,1],[1,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,2],[2,2,1],[1,0,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,2],[2,2,1],[1,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,2],[2,2,1],[1,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [429, 1655] [23, 151, 203, 307, 1223, 1426, 1631, 1632, 1634, 1635, 1638, 1644, 1645, 1648, 1654, 1657, 1658, 3662, 4598] :=
    ⟨Fin 3, «FinitePoly [[0,0,2],[2,2,1],[1,0,2]]», Finite.of_fintype _, by decideFin!⟩
