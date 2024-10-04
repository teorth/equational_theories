
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,1,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,1,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,1,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,1,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4534] [43, 3253, 3456, 3659, 3862, 4065] :=
    ⟨Fin 4, «FinitePoly [[1,3,1,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]», by decideFin!⟩
