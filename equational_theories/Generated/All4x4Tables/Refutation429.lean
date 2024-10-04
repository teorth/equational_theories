
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,1,1],[3,1,0,2],[1,1,3,1],[1,1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,1,1],[3,1,0,2],[1,1,3,1],[1,1,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,1,1],[3,1,0,2],[1,1,3,1],[1,1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,1,1],[3,1,0,2],[1,1,3,1],[1,1,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1975, 2134] [151, 1426, 1629, 1668, 1684, 1691, 1694, 2127, 3862, 3972, 4065, 4606] :=
    ⟨Fin 4, «FinitePoly [[2,1,1,1],[3,1,0,2],[1,1,3,1],[1,1,1,0]]», by decideFin!⟩
