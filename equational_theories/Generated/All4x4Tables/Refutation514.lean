
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,0,5,4],[2,1,4,5,0,3],[5,4,1,2,3,0],[4,5,0,3,2,1],[3,0,5,4,1,2],[0,3,2,1,4,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,0,5,4],[2,1,4,5,0,3],[5,4,1,2,3,0],[4,5,0,3,2,1],[3,0,5,4,1,2],[0,3,2,1,4,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,2,3,0,5,4],[2,1,4,5,0,3],[5,4,1,2,3,0],[4,5,0,3,2,1],[3,0,5,4,1,2],[0,3,2,1,4,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,0,5,4],[2,1,4,5,0,3],[5,4,1,2,3,0],[4,5,0,3,2,1],[3,0,5,4,1,2],[0,3,2,1,4,5]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [669, 2863] [1426, 2035, 2644, 2853, 2855, 2865, 2872, 3253, 3456, 3862, 4065, 4270, 4283, 4598, 4656] :=
    ⟨Fin 6, «FinitePoly [[1,2,3,0,5,4],[2,1,4,5,0,3],[5,4,1,2,3,0],[4,5,0,3,2,1],[3,0,5,4,1,2],[0,3,2,1,4,5]]», by decideFin!⟩
