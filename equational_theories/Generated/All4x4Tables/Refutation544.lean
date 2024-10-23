
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,2,4,4,4],[3,1,1,3,3,1],[0,5,0,0,5,5],[3,1,1,3,3,1],[0,5,0,0,5,5],[2,2,2,4,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,2,4,4,4],[3,1,1,3,3,1],[0,5,0,0,5,5],[3,1,1,3,3,1],[0,5,0,0,5,5],[2,2,2,4,4,4]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[2,2,2,4,4,4],[3,1,1,3,3,1],[0,5,0,0,5,5],[3,1,1,3,3,1],[0,5,0,0,5,5],[2,2,2,4,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,2,4,4,4],[3,1,1,3,3,1],[0,5,0,0,5,5],[3,1,1,3,3,1],[0,5,0,0,5,5],[2,2,2,4,4,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1469] [1428, 1431, 1444, 1451, 4269, 4284] :=
    ⟨Fin 6, «FinitePoly [[2,2,2,4,4,4],[3,1,1,3,3,1],[0,5,0,0,5,5],[3,1,1,3,3,1],[0,5,0,0,5,5],[2,2,2,4,4,4]]», Finite.of_fintype _, by decideFin!⟩
