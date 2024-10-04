
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,0,0,3],[1,3,3,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,0,0,3],[1,3,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,0,0,3],[1,3,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,0,0,3],[1,3,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2296, 2351, 2406] [221, 1629, 2253, 2256, 2263, 2300, 2303, 2327, 2441, 2646, 2659, 2696, 2733, 3065, 3253, 3461, 3519, 3522, 3659, 4065, 4320] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,0,0,3],[1,3,3,3],[0,1,2,3]]», by decideFin!⟩
