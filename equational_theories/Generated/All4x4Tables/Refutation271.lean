
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1633] [151, 203, 1426, 1832, 2238, 2443, 2446, 2449, 3253, 3457, 3458, 3459, 3511, 4120, 4127, 4131, 4598] :=
    ⟨Fin 4, «FinitePoly [[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]», by decideFin!⟩
