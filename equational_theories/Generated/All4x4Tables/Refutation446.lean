
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 3, 1], [3, 1, 3, 1], [2, 0, 2, 0], [2, 2, 2, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 3, 1], [3, 1, 3, 1], [2, 0, 2, 0], [2, 2, 2, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 3, 1], [3, 1, 3, 1], [2, 0, 2, 0], [2, 2, 2, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 3, 1], [3, 1, 3, 1], [2, 0, 2, 0], [2, 2, 2, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2089, 3513, 4357] [151, 2050, 2051, 2124, 2125, 3458, 3459, 3461, 3462, 3464, 3465, 3471, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3862] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 3, 1], [3, 1, 3, 1], [2, 0, 2, 0], [2, 2, 2, 2]]», by decideFin!⟩
