
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,3,1,3],[1,1,1,1],[3,3,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,3],[3,3,1,3],[1,1,1,1],[3,3,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,3],[3,3,1,3],[1,1,1,1],[3,3,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,3],[3,3,1,3],[1,1,1,1],[3,3,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4557] [4408, 4445, 4482, 4599, 4606, 4622] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,3],[3,3,1,3],[1,1,1,1],[3,3,0,3]]», by decideFin!⟩
