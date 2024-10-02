
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 3, 1], [1, 1, 1, 1], [1, 2, 1, 2], [1, 3, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 3, 1], [1, 1, 1, 1], [1, 2, 1, 2], [1, 3, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 3, 1], [1, 1, 1, 1], [1, 2, 1, 2], [1, 3, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 3, 1], [1, 1, 1, 1], [1, 2, 1, 2], [1, 3, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 10, 11, 106, 109, 111, 371, 378, 434, 443, 1053, 1247, 1257, 1265, 1271, 1855, 1863, 3285, 3286, 3726, 3727, 3895, 3931, 4113, 4318, 4673] [13, 427, 439, 854, 1043, 3318, 3863] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 3, 1], [1, 1, 1, 1], [1, 2, 1, 2], [1, 3, 3, 1]]», by decideFin!⟩
