
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,1],[3,2,1,0],[1,0,1,1],[1,0,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,1],[3,2,1,0],[1,0,1,1],[1,0,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,1],[3,2,1,0],[1,0,1,1],[1,0,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,1],[3,2,1,0],[1,0,1,1],[1,0,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1640, 2169] [1426, 1647, 1654, 1657, 1832, 2134, 3261, 3456, 3880, 3887, 3890, 4065, 4380, 4599] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,1],[3,2,1,0],[1,0,1,1],[1,0,1,0]]», by decideFin!⟩
