
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 3, 1], [3, 0, 3, 1], [3, 2, 3, 1], [3, 2, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 3, 1], [3, 0, 3, 1], [3, 2, 3, 1], [3, 2, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 3, 1], [3, 0, 3, 1], [3, 2, 3, 1], [3, 2, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 3, 1], [3, 0, 3, 1], [3, 2, 3, 1], [3, 2, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [58, 4360] [3, 8, 23, 48, 50, 53, 56, 62, 63, 65, 66, 72, 73, 75, 99, 151, 203, 255, 307, 375, 411, 615, 617, 620, 623, 630, 633, 640, 643, 666, 667, 669, 670, 676, 677, 679, 680, 703, 704, 706, 707, 713, 714, 716, 818, 820, 823, 826, 833, 836, 843, 846, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4118, 4121, 4128, 4380, 4599] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 3, 1], [3, 0, 3, 1], [3, 2, 3, 1], [3, 2, 3, 1]]», by decideFin!⟩
