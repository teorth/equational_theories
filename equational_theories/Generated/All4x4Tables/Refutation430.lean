
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,2,3],[3,3,2,3],[1,3,2,3],[3,3,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,2,3],[3,3,2,3],[1,3,2,3],[3,3,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,2,3],[3,3,2,3],[1,3,2,3],[3,3,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,2,3],[3,3,2,3],[1,3,2,3],[3,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [318, 4569] [4396, 4406, 4435, 4445, 4470, 4480, 4599, 4622, 4631, 4635] :=
    ⟨Fin 4, «FinitePoly [[3,3,2,3],[3,3,2,3],[1,3,2,3],[3,3,2,3]]», by decideFin!⟩
