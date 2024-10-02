
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 3, 1], [3, 2, 3, 1], [2, 2, 3, 1], [3, 2, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [2, 2, 3, 1], [3, 2, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 3, 1], [3, 2, 3, 1], [2, 2, 3, 1], [3, 2, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [2, 2, 3, 1], [3, 2, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [52, 378, 635, 3897, 4073] [55, 56, 63, 75, 364, 617, 619, 620, 622, 630, 639, 642, 643, 820, 823, 833, 835, 845, 1426, 3253, 3925, 3928, 4067, 4080, 4090, 4587] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [2, 2, 3, 1], [3, 2, 3, 1]]», by decideFin!⟩
