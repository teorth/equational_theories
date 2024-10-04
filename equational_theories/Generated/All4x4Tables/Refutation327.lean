
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,0,0],[3,2,1,1],[2,2,2,2],[3,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,0,0],[3,2,1,1],[2,2,2,2],[3,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,0,0],[3,2,1,1],[2,2,2,2],[3,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,0,0],[3,2,1,1],[2,2,2,2],[3,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [434] [361, 838, 1043, 1053, 1056, 1240, 1245, 1246, 1263, 1264, 1267, 3321, 3724, 3931] :=
    ⟨Fin 4, «FinitePoly [[2,3,0,0],[3,2,1,1],[2,2,2,2],[3,3,3,2]]», by decideFin!⟩
