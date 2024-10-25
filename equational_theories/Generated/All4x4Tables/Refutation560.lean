
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,3,3],[3,2,2,2],[1,1,1,0],[0,0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,3,3],[3,2,2,2],[1,1,1,0],[0,0,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,3,3],[3,2,2,2],[1,1,1,0],[0,0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,3,3],[3,2,2,2],[1,1,1,0],[0,0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1453, 1456] [151, 1428, 2257, 3058, 3066, 3075, 3456, 4314, 4598, 4656] :=
    ⟨Fin 4, «FinitePoly [[2,3,3,3],[3,2,2,2],[1,1,1,0],[0,0,0,1]]», Finite.of_fintype _, by decideFin!⟩
