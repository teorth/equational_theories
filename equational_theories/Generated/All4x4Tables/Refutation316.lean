
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,2,3],[2,3,0,1],[3,2,1,0],[1,0,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,2,3],[2,3,0,1],[3,2,1,0],[1,0,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,2,3],[2,3,0,1],[3,2,1,0],[1,0,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,2,3],[2,3,0,1],[3,2,1,0],[1,0,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1655, 1685, 1691] [8, 255, 264, 271, 283, 411, 513, 1020, 1029, 1039, 1045, 1075, 1083, 1110, 1122, 1638, 1832, 3319, 3862] :=
    ⟨Fin 4, «FinitePoly [[1,1,2,3],[2,3,0,1],[3,2,1,0],[1,0,3,2]]», by decideFin!⟩
