
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 0, 1], [2, 0, 1, 1], [2, 3, 1, 2], [3, 3, 0, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 0, 1], [2, 0, 1, 1], [2, 3, 1, 2], [3, 3, 0, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 0, 1], [2, 0, 1, 1], [2, 3, 1, 2], [3, 3, 0, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 0, 1], [2, 0, 1, 1], [2, 3, 1, 2], [3, 3, 0, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [52, 55, 378, 629, 639, 835, 1035, 1045] [3, 8, 23, 49, 99, 151, 203, 255, 307, 361, 364, 375, 411, 616, 619, 622, 632, 642, 819, 825, 845, 1021, 1022, 1023, 1025, 1026, 1028, 1029, 1036, 1038, 1039, 1046, 1048, 1049, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4067, 4070, 4073, 4080, 4090, 4118, 4121, 4128, 4155, 4269, 4380, 4584, 4599] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 0, 1], [2, 0, 1, 1], [2, 3, 1, 2], [3, 3, 0, 2]]», by decideFin!⟩
