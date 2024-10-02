
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 0, 3], [3, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 0, 3], [3, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 0, 3], [3, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 0, 3], [3, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [307, 1020, 1240, 1244, 3255, 3661, 3662, 3724] [8, 100, 101, 102, 105, 107, 108, 114, 115, 117, 118, 124, 125, 127, 308, 309, 310, 312, 313, 315, 323, 325, 326, 333, 335, 359, 411, 817, 1022, 1025, 1028, 1045, 1231, 1242, 1249, 1251, 1278, 1288, 1832, 3256, 3319, 3665, 3712, 3719, 3862, 4065] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 0, 3], [3, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 3]]», by decideFin!⟩
