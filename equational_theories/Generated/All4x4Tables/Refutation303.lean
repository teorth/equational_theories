
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,3],[3,3,1,3],[0,3,3,0],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,3],[3,3,1,3],[0,3,3,0],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,3],[3,3,1,3],[0,3,3,0],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,3],[3,3,1,3],[0,3,3,0],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2517, 2687] [203, 2238, 2449, 2456, 2533, 2571, 2588, 2646, 2696, 2709, 3253, 3458, 3461, 3519, 3664, 3674, 3749, 4272, 4314, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,3],[3,3,1,3],[0,3,3,0],[0,1,2,3]]», by decideFin!⟩
