
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 0, 1], [2, 0, 1, 2], [2, 2, 2, 2], [3, 3, 3, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 0, 1], [2, 0, 1, 2], [2, 2, 2, 2], [3, 3, 3, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 0, 1], [2, 0, 1, 2], [2, 2, 2, 2], [3, 3, 3, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 0, 1], [2, 0, 1, 2], [2, 2, 2, 2], [3, 3, 3, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [107, 1228, 1241, 1250, 1252] [104, 105, 108, 411, 832, 833, 835, 1021, 1022, 1023, 1025, 1026, 1028, 1029, 1035, 1036, 1038, 1039, 1046, 1048, 1049, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1225, 1238, 1251, 3253, 3862, 4591] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 0, 1], [2, 0, 1, 2], [2, 2, 2, 2], [3, 3, 3, 0]]», by decideFin!⟩
