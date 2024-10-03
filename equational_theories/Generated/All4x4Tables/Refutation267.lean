import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,2,3],[3,3,0,3],[0,1,0,3],[0,1,2,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,2,3],[3,3,0,3],[0,1,0,3],[0,1,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,2,3],[3,3,0,3],[0,1,0,3],[0,1,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,2,3],[3,3,0,3],[0,1,0,3],[0,1,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2310] [2253,2327,2364,3659,3759,4320] :=
    ⟨Fin 4, «FinitePoly [[3,0,2,3],[3,3,0,3],[0,1,0,3],[0,1,2,2]]», by decideFin!⟩
