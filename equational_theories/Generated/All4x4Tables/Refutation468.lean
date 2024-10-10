
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,4,3],[1,3,0,2,4],[2,0,4,3,1],[3,4,2,1,0],[4,1,3,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,4,3],[1,3,0,2,4],[2,0,4,3,1],[3,4,2,1,0],[4,1,3,0,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,1,4,3],[1,3,0,2,4],[2,0,4,3,1],[3,4,2,1,0],[4,1,3,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,4,3],[1,3,0,2,4],[2,0,4,3,1],[3,4,2,1,0],[4,1,3,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1061, 1073] [419, 427, 436, 614, 817, 1023, 1028, 1036, 1045, 1075, 1223, 1426, 1629, 1832, 2035, 2238, 2459, 3253, 3659, 3862, 4270, 4598, 4647] :=
    ⟨Fin 5, «FinitePoly [[0,2,1,4,3],[1,3,0,2,4],[2,0,4,3,1],[3,4,2,1,0],[4,1,3,0,2]]», by decideFin!⟩
