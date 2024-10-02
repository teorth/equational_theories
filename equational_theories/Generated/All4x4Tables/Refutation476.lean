
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 0, 3], [1, 1, 1, 1], [1, 2, 1, 2], [2, 3, 1, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 0, 3], [1, 1, 1, 1], [1, 2, 1, 2], [2, 3, 1, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 0, 3], [1, 1, 1, 1], [1, 2, 1, 2], [2, 3, 1, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 0, 3], [1, 1, 1, 1], [1, 2, 1, 2], [2, 3, 1, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 11, 109, 368, 1022, 1053, 1060, 1229, 1242, 1257, 1267, 3286, 3895, 3902, 3906, 4109, 4636] [101, 104, 105, 378, 413, 427, 429, 832, 833, 836, 1031, 1042, 1228, 1238, 1241, 1245, 1851, 3863, 4131] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 0, 3], [1, 1, 1, 1], [1, 2, 1, 2], [2, 3, 1, 1]]», by decideFin!⟩
