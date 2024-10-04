
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,2,3],[3,2,2,3],[0,1,2,3],[0,1,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,2,3],[3,2,2,3],[0,1,2,3],[0,1,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,2,3],[3,2,2,3],[0,1,2,3],[0,1,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,2,3],[3,2,2,3],[0,1,2,3],[0,1,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3145] [2296, 2333, 2351, 2368, 2389, 2402, 2517, 2536, 2558, 2665, 3529, 3749, 4175] :=
    ⟨Fin 4, «FinitePoly [[2,3,2,3],[3,2,2,3],[0,1,2,3],[0,1,2,2]]», by decideFin!⟩
