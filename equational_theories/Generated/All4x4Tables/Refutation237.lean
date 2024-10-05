
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3],[2,3,0,3],[0,3,3,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,3],[2,3,0,3],[0,3,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,3],[2,3,0,3],[0,3,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,3],[2,3,0,3],[0,3,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2368, 2402, 2571, 3269] [2256, 2300, 2314, 2351, 2449, 2476, 2517, 3255, 3271, 3467, 3519, 3749, 4131, 4269, 4320] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,3],[2,3,0,3],[0,3,3,3],[0,1,2,3]]», by decideFin!⟩
