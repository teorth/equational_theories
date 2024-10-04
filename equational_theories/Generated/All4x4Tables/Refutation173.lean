
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,0],[3,1,1,1],[3,2,2,2],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,0],[3,1,1,1],[3,2,2,2],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,0],[3,1,1,1],[3,2,2,2],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,0],[3,1,1,1],[3,2,2,2],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [618, 834, 837, 839, 1245, 1259, 1260] [100, 361, 427, 430, 439, 820, 823, 1224, 1226, 3318, 3918] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,0],[3,1,1,1],[3,2,2,2],[3,3,3,3]]», by decideFin!⟩
