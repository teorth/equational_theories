
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,0,1],[2,2,1,1],[2,2,2,2],[0,2,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,0,1],[2,2,1,1],[2,2,2,2],[0,2,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,0,1],[2,2,1,1],[2,2,2,2],[0,2,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,0,1],[2,2,1,1],[2,2,2,2],[0,2,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1060, 1243, 1245, 4097] [101, 837, 1035, 1038, 1042, 1048, 1052, 1056, 1228, 1238, 1834, 1847, 3306, 3316, 3726, 3925, 4070, 4084, 4131, 4269, 4314, 4598, 4631] :=
    ⟨Fin 4, «FinitePoly [[2,0,0,1],[2,2,1,1],[2,2,2,2],[0,2,3,2]]», by decideFin!⟩
