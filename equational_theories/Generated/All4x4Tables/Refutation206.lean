
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,1],[2,2,1,0],[2,2,2,2],[2,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,0,1],[2,2,1,0],[2,2,2,2],[2,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,0,1],[2,2,1,0],[2,2,2,2],[2,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,0,1],[2,2,1,0],[2,2,2,2],[2,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1042, 1245, 1257, 1259, 1267] [1025, 1045, 1229, 1241, 3306] :=
    ⟨Fin 4, «FinitePoly [[2,1,0,1],[2,2,1,0],[2,2,2,2],[2,3,3,2]]», by decideFin!⟩
