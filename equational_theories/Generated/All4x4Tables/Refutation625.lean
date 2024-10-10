
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,5,0,5,6,7],[4,1,5,1,4,5,1,5],[4,6,2,6,4,2,6,2],[4,7,7,3,4,7,3,7],[4,1,2,3,4,5,6,7],[0,1,5,5,4,5,6,5],[0,6,2,6,4,5,6,2],[0,7,7,3,4,7,3,7]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,5,0,5,6,7],[4,1,5,1,4,5,1,5],[4,6,2,6,4,2,6,2],[4,7,7,3,4,7,3,7],[4,1,2,3,4,5,6,7],[0,1,5,5,4,5,6,5],[0,6,2,6,4,5,6,2],[0,7,7,3,4,7,3,7]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[0,2,3,5,0,5,6,7],[4,1,5,1,4,5,1,5],[4,6,2,6,4,2,6,2],[4,7,7,3,4,7,3,7],[4,1,2,3,4,5,6,7],[0,1,5,5,4,5,6,5],[0,6,2,6,4,5,6,2],[0,7,7,3,4,7,3,7]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,5,0,5,6,7],[4,1,5,1,4,5,1,5],[4,6,2,6,4,2,6,2],[4,7,7,3,4,7,3,7],[4,1,2,3,4,5,6,7],[0,1,5,5,4,5,6,5],[0,6,2,6,4,5,6,2],[0,7,7,3,4,7,3,7]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2890] [2646, 2652, 2659, 2662, 2669, 2849, 2852, 2865, 2872, 3306, 4599, 4631] :=
    ⟨Fin 8, «FinitePoly [[0,2,3,5,0,5,6,7],[4,1,5,1,4,5,1,5],[4,6,2,6,4,2,6,2],[4,7,7,3,4,7,3,7],[4,1,2,3,4,5,6,7],[0,1,5,5,4,5,6,5],[0,6,2,6,4,5,6,2],[0,7,7,3,4,7,3,7]]», by decideFin!⟩
