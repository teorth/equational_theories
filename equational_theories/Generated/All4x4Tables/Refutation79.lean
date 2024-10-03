import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,1],[3,3,1,2],[3,3,1,2],[3,0,1,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,1],[3,3,1,2],[3,3,1,2],[3,0,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,1],[3,3,1,2],[3,3,1,2],[3,0,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,1],[3,3,1,2],[3,3,1,2],[3,0,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1484] [3864,3880,3883,3915,3921,3952,3958,3989,3997,4001,4587,4615,4645,4666,4689] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,1],[3,3,1,2],[3,3,1,2],[3,0,1,1]]», by decideFin!⟩
