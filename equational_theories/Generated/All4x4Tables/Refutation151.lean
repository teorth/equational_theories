
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,3,3],[3,1,2,2],[3,1,2,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,3,3],[3,1,2,2],[3,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,3,3],[3,1,2,2],[3,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,3,3],[3,1,2,2],[3,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2513, 2716] [1045, 1921, 2300, 2327, 2337, 2540, 2743, 3068, 3346, 3353, 3546, 3759, 3887, 4320, 4445] :=
    ⟨Fin 4, «FinitePoly [[0,3,3,3],[3,1,2,2],[3,1,2,3],[0,1,2,3]]», by decideFin!⟩
