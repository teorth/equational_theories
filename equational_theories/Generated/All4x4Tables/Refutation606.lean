
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,0,3,4,5],[2,5,2,5,5,5],[2,1,2,3,4,5],[0,1,2,4,4,4],[0,5,2,5,5,5],[0,3,2,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,0,3,4,5],[2,5,2,5,5,5],[2,1,2,3,4,5],[0,1,2,4,4,4],[0,5,2,5,5,5],[0,3,2,3,3,3]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,1,0,3,4,5],[2,5,2,5,5,5],[2,1,2,3,4,5],[0,1,2,4,4,4],[0,5,2,5,5,5],[0,3,2,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,0,3,4,5],[2,5,2,5,5,5],[2,1,2,3,4,5],[0,1,2,4,4,4],[0,5,2,5,5,5],[0,3,2,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2683] [2035, 2646, 2659, 2669, 2849, 2852, 2865, 2872, 2890, 3309, 3319, 3509, 3519, 3522, 4284, 4631] :=
    ⟨Fin 6, «FinitePoly [[0,1,0,3,4,5],[2,5,2,5,5,5],[2,1,2,3,4,5],[0,1,2,4,4,4],[0,5,2,5,5,5],[0,3,2,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
