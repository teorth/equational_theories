
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 0, 3], [1, 1, 1, 1], [2, 2, 1, 1], [2, 3, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 0, 3], [1, 1, 1, 1], [2, 2, 1, 1], [2, 3, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 0, 3], [1, 1, 1, 1], [2, 2, 1, 1], [2, 3, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 0, 3], [1, 1, 1, 1], [2, 2, 1, 1], [2, 3, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [104, 109, 368, 427, 1053, 1060, 1257, 1262, 3895, 3902] [16, 101, 102, 105, 114, 115, 117, 118, 124, 125, 127, 378, 419, 466, 500, 504, 513, 906, 910, 1046, 1075, 1109, 1122, 1229, 1231, 1239, 1242, 1244, 1278, 1312, 1325, 1850, 3863, 4070, 4071, 4073, 4081, 4083, 4084, 4131] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 0, 3], [1, 1, 1, 1], [2, 2, 1, 1], [2, 3, 0, 1]]», by decideFin!⟩
