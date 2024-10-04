
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0],[0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0],[0,0]]» : Magma (Fin 2) where
  op := memoFinOp fun x y => [[0,0],[0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0],[0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [41] [2, 3, 8, 23, 47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050] :=
    ⟨Fin 2, «FinitePoly [[0,0],[0,0]]», by decideFin!⟩
