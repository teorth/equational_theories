
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2592] [1629, 2238, 2449, 2466, 2496, 2530, 2644, 2847, 3058, 3075, 3105, 3456, 3659, 4065, 4320, 4622] :=
    ⟨Fin 5, «FinitePoly [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]», by decideFin!⟩
