
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,4,0,2,4,0],[2,1,3,2,1,3],[2,1,0,2,1,0],[5,1,3,5,1,3],[5,4,0,5,4,0],[5,4,3,5,4,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,4,0,2,4,0],[2,1,3,2,1,3],[2,1,0,2,1,0],[5,1,3,5,1,3],[5,4,0,5,4,0],[5,4,3,5,4,3]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[2,4,0,2,4,0],[2,1,3,2,1,3],[2,1,0,2,1,0],[5,1,3,5,1,3],[5,4,0,5,4,0],[5,4,3,5,4,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,4,0,2,4,0],[2,1,3,2,1,3],[2,1,0,2,1,0],[5,1,3,5,1,3],[5,4,0,5,4,0],[5,4,3,5,4,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2066] [2040, 2043, 2050, 2053, 4599, 4631] :=
    ⟨Fin 6, «FinitePoly [[2,4,0,2,4,0],[2,1,3,2,1,3],[2,1,0,2,1,0],[5,1,3,5,1,3],[5,4,0,5,4,0],[5,4,3,5,4,3]]», by decideFin!⟩
