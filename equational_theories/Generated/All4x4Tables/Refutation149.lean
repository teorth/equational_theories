
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1029, 4091] [56, 159, 255, 359, 411, 619, 642, 825, 832, 845, 1038, 1039, 1045, 1241, 1434, 1444, 1451, 1629, 1832, 2043, 2256, 2264, 2449, 2457, 2459, 3058, 3066, 3075, 3253, 3459, 3462, 3511, 3518, 3659, 3862, 4070, 4073, 4074, 4083, 4120, 4127, 4128, 4130, 4598, 4647, 4656] :=
    ⟨Fin 4, «FinitePoly [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]», by decideFin!⟩
