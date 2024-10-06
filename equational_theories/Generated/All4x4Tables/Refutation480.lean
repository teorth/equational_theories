
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,2,4,3],[2,3,0,1,4],[3,1,4,0,2],[0,4,3,2,1],[4,2,1,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,2,4,3],[2,3,0,1,4],[3,1,4,0,2],[0,4,3,2,1],[4,2,1,3,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,0,2,4,3],[2,3,0,1,4],[3,1,4,0,2],[0,4,3,2,1],[4,2,1,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,2,4,3],[2,3,0,1,4],[3,1,4,0,2],[0,4,3,2,1],[4,2,1,3,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [474, 2722, 2743] [47, 99, 151, 203, 255, 307, 614, 817, 1223, 1426, 2035, 2238, 2441, 2847, 3315, 3456, 3659, 3865, 3870, 3917, 3955, 4065, 4380, 4656] :=
    ⟨Fin 5, «FinitePoly [[1,0,2,4,3],[2,3,0,1,4],[3,1,4,0,2],[0,4,3,2,1],[4,2,1,3,0]]», by decideFin!⟩
