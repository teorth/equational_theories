
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,1],[3,1,1,3],[3,2,2,0],[1,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,1],[3,1,1,3],[3,2,2,0],[1,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,1],[3,1,1,3],[3,2,2,0],[1,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,1],[3,1,1,3],[3,2,2,0],[1,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [455, 647, 655, 861, 1061, 1264, 1267] [1426, 1629, 1838, 1840, 1848, 2035, 2238, 2441, 2644, 2847, 3050, 3259, 3261, 3306, 3308, 3456, 3665, 3667, 3712, 3714, 3865, 3868, 3917, 3924, 4065, 4283, 4380, 4656, 4673] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,1],[3,1,1,3],[3,2,2,0],[1,3,3,2]]», by decideFin!⟩
