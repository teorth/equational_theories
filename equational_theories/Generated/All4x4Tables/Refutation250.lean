
import equational_theories.AllEquations
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
  ∃ (G : Type) (_ : Magma G), Facts G [476, 503, 510, 727, 964, 1594, 3566, 3790] [49, 52, 55, 62, 65, 72, 361, 413, 416, 419, 426, 429, 436, 463, 466, 473, 500, 513, 616, 622, 629, 632, 639, 642, 666, 669, 676, 679, 703, 713, 819, 822, 825, 835, 842, 845, 869, 872, 879, 906, 909, 916, 1428, 1431, 1434, 1441, 1444, 1451, 1481, 1488, 1491, 1515, 1518, 1525, 3261, 3278, 3306, 3864, 3870, 3880, 3890, 3918, 3928, 3955, 4067, 4073, 4083, 4093, 4096, 4104, 4121, 4131, 4158, 4269, 4272, 4275, 4284, 4291, 4584, 4590, 4599, 4635] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[0,1,2,3],[0,1,2,3],[1,2,0,3]]», by decideFin!⟩
