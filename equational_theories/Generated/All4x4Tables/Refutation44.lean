
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 1, 1], [1, 1, 1, 1], [1, 2, 0, 1], [0, 3, 1, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 1, 1], [1, 1, 1, 1], [1, 2, 0, 1], [0, 3, 1, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 1, 1], [1, 1, 1, 1], [1, 2, 0, 1], [0, 3, 1, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 1, 1], [1, 1, 1, 1], [1, 2, 0, 1], [0, 3, 1, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [56, 1035, 1050, 4276] [2, 3, 8, 23, 38, 39, 40, 43, 48, 49, 50, 52, 53, 55, 62, 63, 65, 66, 72, 73, 75, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1022, 1023, 1025, 1026, 1028, 1029, 1036, 1038, 1039, 1045, 1046, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 1, 1], [1, 1, 1, 1], [1, 2, 0, 1], [0, 3, 1, 2]]», by decideFin!⟩
