
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[2,3,2,3],[2,1,3,3],[2,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,3,3],[2,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[2,3,2,3],[2,1,3,3],[2,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,3,3],[2,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3492, 3680] [3253, 3459, 3481, 3509, 3519, 3522, 3712, 3749, 3759, 4065, 4269, 4272, 4273, 4276, 4314, 4320, 4343, 4606, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,3,3],[2,3,3,3]]», by decideFin!⟩
