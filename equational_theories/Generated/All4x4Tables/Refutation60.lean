
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,0,1],[3,1,1,0],[0,2,2,3],[1,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,0,1],[3,1,1,0],[0,2,2,3],[1,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,0,1],[3,1,1,0],[0,2,2,3],[1,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,0,1],[3,1,1,0],[0,2,2,3],[1,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1264, 1267, 2688, 4477] [2041, 2043, 2053, 2647, 2650, 2662, 2669, 2853, 2855, 2863, 2865, 3259, 3261, 3306, 3308, 3462, 3464, 3509, 3511, 3665, 4283, 4396, 4398, 4433, 4435] :=
    ⟨Fin 4, «FinitePoly [[2,0,0,1],[3,1,1,0],[0,2,2,3],[1,3,3,2]]», by decideFin!⟩
