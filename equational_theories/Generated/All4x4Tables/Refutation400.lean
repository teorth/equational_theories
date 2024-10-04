import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,0,2,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,0,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,0,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,0,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1479,1480] [151,152,166,167,168,1428,1429,1430,3456,3461] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,0,2,1]]», by decideFin!⟩
