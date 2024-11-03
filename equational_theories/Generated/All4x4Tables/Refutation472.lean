
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[0,1,2,3],[0,1,2,3],[1,2,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[0,1,2,3],[0,1,2,3],[1,2,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[0,1,2,3],[0,1,2,3],[1,2,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[0,1,2,3],[0,1,2,3],[1,2,0,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [476, 503, 964, 3566, 3790] [55, 65, 616, 622, 629, 632, 639, 642, 669, 676, 679, 713, 819, 822, 825, 835, 842, 845, 872, 879, 906, 1428, 1431, 1434, 1441, 1444, 1451, 1488, 1491, 1515, 1518, 1525, 3306, 3864, 3870, 3880, 3890, 3918, 3928, 3955, 4067, 4073, 4083, 4093, 4121, 4131, 4158, 4269, 4272, 4275, 4284, 4291, 4599, 4622, 4631, 4635] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[0,1,2,3],[0,1,2,3],[1,2,0,3]]», Finite.of_fintype _, by decideFin!⟩
