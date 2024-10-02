
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 1, 3, 3], [2, 2, 2, 3], [0, 0, 0, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 1, 3, 3], [2, 2, 2, 3], [0, 0, 0, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 1, 3, 3], [2, 2, 2, 3], [0, 0, 0, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 1, 3, 3], [2, 2, 2, 3], [0, 0, 0, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [257, 263, 323, 2662, 2849, 2855] [260, 309, 2035, 2659, 2669, 2672, 2852, 2862, 2865, 2872, 2875, 3255, 3261, 3456, 4269, 4584] :=
    ⟨Fin 4, «FinitePoly [[1, 1, 3, 3], [2, 2, 2, 3], [0, 0, 0, 3], [0, 1, 2, 3]]», by decideFin!⟩
