
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,2,1],[3,3,0,0],[3,3,2,0],[3,3,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,2,1],[3,3,0,0],[3,3,2,0],[3,3,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,2,1],[3,3,0,0],[3,3,2,0],[3,3,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,2,1],[3,3,0,0],[3,3,2,0],[3,3,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1664] [1637, 1657, 3253, 4599] :=
    ⟨Fin 4, «FinitePoly [[1,2,2,1],[3,3,0,0],[3,3,2,0],[3,3,2,1]]», by decideFin!⟩
