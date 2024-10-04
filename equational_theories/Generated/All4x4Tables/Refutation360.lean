
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,1,1],[2,0,3,2],[1,0,3,1],[2,0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,1,1],[2,0,3,2],[1,0,3,1],[2,0,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,1,1],[2,0,3,2],[1,0,3,1],[2,0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,1,1],[2,0,3,2],[1,0,3,1],[2,0,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1681] [99, 151, 411, 1020, 1223, 1631, 1634, 1637, 1644, 1647, 1654, 1657, 1684, 1691, 1694, 1718, 1721, 1728, 1731, 1832, 2035, 3253, 3864, 3867, 3870, 3880, 3887, 3890, 3915, 3918, 3925, 3928, 3952, 3955, 3962, 4065, 4269, 4272, 4275, 4284, 4291, 4320, 4584, 4587, 4590, 4599] :=
    ⟨Fin 4, «FinitePoly [[2,3,1,1],[2,0,3,2],[1,0,3,1],[2,0,0,1]]», by decideFin!⟩
