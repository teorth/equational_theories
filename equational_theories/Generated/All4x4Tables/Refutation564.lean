
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,0,0,3],[3,4,4,1,4],[3,1,3,3,3],[2,2,2,2,3],[2,1,4,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,0,0,3],[3,4,4,1,4],[3,1,3,3,3],[2,2,2,2,3],[2,1,4,1,1]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,0,0,3],[3,4,4,1,4],[3,1,3,3,3],[2,2,2,2,3],[2,1,4,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,0,0,3],[3,4,4,1,4],[3,1,3,3,3],[2,2,2,2,3],[2,1,4,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1849] [2449, 3459] :=
    ⟨Fin 5, «FinitePoly [[0,2,0,0,3],[3,4,4,1,4],[3,1,3,3,3],[2,2,2,2,3],[2,1,4,1,1]]», by decideFin!⟩
