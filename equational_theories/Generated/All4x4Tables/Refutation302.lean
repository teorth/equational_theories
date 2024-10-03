import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,3,3],[3,2,2,3],[3,1,3,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,3,3],[3,2,2,3],[3,1,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,3,3],[3,2,2,3],[3,1,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,3,3],[3,2,2,3],[3,1,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2364,2739] [3659,3674,3684,3749,3759] :=
    ⟨Fin 4, «FinitePoly [[0,3,3,3],[3,2,2,3],[3,1,3,3],[0,1,2,3]]», by decideFin!⟩
