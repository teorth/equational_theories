
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,3,2,0],[1,2,4,4,2],[2,2,2,2,2],[2,3,0,2,0],[1,3,1,4,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,3,2,0],[1,2,4,4,2],[2,2,2,2,2],[2,3,0,2,0],[1,3,1,4,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[2,3,3,2,0],[1,2,4,4,2],[2,2,2,2,2],[2,3,0,2,0],[1,3,1,4,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,3,2,0],[1,2,4,4,2],[2,2,2,2,2],[2,3,0,2,0],[1,3,1,4,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1855] [1834, 1850, 1860, 3253, 4070, 4071, 4073, 4598, 4631] :=
    ⟨Fin 5, «FinitePoly [[2,3,3,2,0],[1,2,4,4,2],[2,2,2,2,2],[2,3,0,2,0],[1,3,1,4,2]]», by decideFin!⟩
