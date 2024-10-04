
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [221, 2277, 2281, 2314, 2318, 2368, 2372] [208, 231, 1629, 2240, 2263, 2327, 2340, 2441, 2605, 2644, 3050, 3139, 3152, 3253, 3458, 3522, 3664, 3674, 3677, 3749, 3759, 4065, 4090, 4118, 4165, 4272, 4622] :=
    ⟨Fin 4, «FinitePoly [[0,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]», by decideFin!⟩
