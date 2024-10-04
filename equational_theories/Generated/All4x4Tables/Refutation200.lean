
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,0,1],[3,1,0,1],[3,1,0,1],[3,3,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,0,1],[3,1,0,1],[3,1,0,1],[3,3,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,0,1],[3,1,0,1],[3,1,0,1],[3,3,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,0,1],[3,1,0,1],[3,1,0,1],[3,3,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3939] [3915, 3925, 3943, 4076, 4121, 4134, 4146, 4599, 4675] :=
    ⟨Fin 4, «FinitePoly [[3,1,0,1],[3,1,0,1],[3,1,0,1],[3,3,0,3]]», by decideFin!⟩
