
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,1,4,3],[3,2,1,0,0],[1,2,1,4,3],[4,0,1,4,0],[3,0,1,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,1,4,3],[3,2,1,0,0],[1,2,1,4,3],[4,0,1,4,0],[3,0,1,0,3]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,1,4,3],[3,2,1,0,0],[1,2,1,4,3],[4,0,1,4,0],[3,0,1,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,1,4,3],[3,2,1,0,0],[1,2,1,4,3],[4,0,1,4,0],[3,0,1,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2169] [151, 1426, 1631, 1637, 1654, 1657, 1832, 2050, 2124, 2134, 3261, 3306, 3309, 3456, 3880, 3887, 3890, 3952, 4065, 4284, 4380, 4599, 4606, 4635] :=
    ⟨Fin 5, «FinitePoly [[1,2,1,4,3],[3,2,1,0,0],[1,2,1,4,3],[4,0,1,4,0],[3,0,1,0,3]]», by decideFin!⟩
