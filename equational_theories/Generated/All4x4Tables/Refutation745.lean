
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,4,6,2,6,4,4,2],[4,2,4,5,2,3,0,7,2],[8,8,3,3,3,0,1,2,5],[8,8,2,3,7,0,1,2,5],[8,8,7,2,3,0,1,3,5],[2,4,4,7,2,2,3,4,6],[3,2,4,7,2,4,2,4,4],[8,8,3,2,7,0,1,3,5],[1,5,4,7,2,2,3,7,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,4,6,2,6,4,4,2],[4,2,4,5,2,3,0,7,2],[8,8,3,3,3,0,1,2,5],[8,8,2,3,7,0,1,2,5],[8,8,7,2,3,0,1,3,5],[2,4,4,7,2,2,3,4,6],[3,2,4,7,2,4,2,4,4],[8,8,3,2,7,0,1,3,5],[1,5,4,7,2,2,3,7,2]]» : Magma (Fin 9) where
  op := memoFinOp fun x y => [[2,3,4,6,2,6,4,4,2],[4,2,4,5,2,3,0,7,2],[8,8,3,3,3,0,1,2,5],[8,8,2,3,7,0,1,2,5],[8,8,7,2,3,0,1,3,5],[2,4,4,7,2,2,3,4,6],[3,2,4,7,2,4,2,4,4],[8,8,3,2,7,0,1,3,5],[1,5,4,7,2,2,3,7,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,4,6,2,6,4,4,2],[4,2,4,5,2,3,0,7,2],[8,8,3,3,3,0,1,2,5],[8,8,2,3,7,0,1,2,5],[8,8,7,2,3,0,1,3,5],[2,4,4,7,2,2,3,4,6],[3,2,4,7,2,4,2,4,4],[8,8,3,2,7,0,1,3,5],[1,5,4,7,2,2,3,7,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3475] [3659] :=
    ⟨Fin 9, «FinitePoly [[2,3,4,6,2,6,4,4,2],[4,2,4,5,2,3,0,7,2],[8,8,3,3,3,0,1,2,5],[8,8,2,3,7,0,1,2,5],[8,8,7,2,3,0,1,3,5],[2,4,4,7,2,2,3,4,6],[3,2,4,7,2,4,2,4,4],[8,8,3,2,7,0,1,3,5],[1,5,4,7,2,2,3,7,2]]», Finite.of_fintype _, by decideFin!⟩
