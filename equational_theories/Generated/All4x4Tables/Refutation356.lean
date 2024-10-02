
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 0, 1], [2, 2, 1, 2], [2, 2, 2, 2], [2, 1, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 0, 1], [2, 2, 1, 2], [2, 2, 2, 2], [2, 1, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 0, 1], [2, 2, 1, 2], [2, 2, 2, 2], [2, 1, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 0, 1], [2, 2, 1, 2], [2, 2, 2, 2], [2, 1, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 104, 105, 108, 1045, 1048, 1049, 1240, 1243, 1244, 1245, 1253, 1255, 1259, 1263, 4591] [100, 101, 102, 107, 114, 115, 117, 118, 124, 125, 127, 411, 817, 1022, 1028, 1046, 1109, 1250, 1254, 1262, 1278, 1288, 1325, 1629, 2035, 4587, 4590, 4599] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 0, 1], [2, 2, 1, 2], [2, 2, 2, 2], [2, 1, 3, 1]]», by decideFin!⟩
