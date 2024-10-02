
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 2, 0, 3], [3, 2, 1, 3], [2, 1, 3, 2], [1, 3, 2, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 2, 0, 3], [3, 2, 1, 3], [2, 1, 3, 2], [1, 3, 2, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 2, 0, 3], [3, 2, 1, 3], [2, 1, 3, 2], [1, 3, 2, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 2, 0, 3], [3, 2, 1, 3], [2, 1, 3, 2], [1, 3, 2, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1029, 4068, 4091, 4608] [3, 8, 23, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1021, 1022, 1023, 1025, 1026, 1028, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1049, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4070, 4073, 4074, 4083, 4118, 4130, 4158, 4164, 4269, 4273, 4290, 4380, 4584, 4588, 4605] :=
    ⟨Fin 4, «FinitePoly [[1, 2, 0, 3], [3, 2, 1, 3], [2, 1, 3, 2], [1, 3, 2, 1]]», by decideFin!⟩
