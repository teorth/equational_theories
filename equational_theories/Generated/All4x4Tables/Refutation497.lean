
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 3, 1], [3, 0, 3, 1], [3, 2, 0, 1], [3, 0, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 3, 1], [3, 0, 3, 1], [3, 2, 0, 1], [3, 0, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 3, 1], [3, 0, 3, 1], [3, 2, 0, 1], [3, 0, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 3, 1], [3, 0, 3, 1], [3, 2, 0, 1], [3, 0, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [619, 657, 4590] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 359, 411, 615, 616, 617, 620, 623, 630, 632, 633, 639, 640, 643, 666, 667, 669, 670, 676, 677, 679, 680, 703, 704, 706, 707, 713, 714, 716, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 3, 1], [3, 0, 3, 1], [3, 2, 0, 1], [3, 0, 3, 1]]», by decideFin!⟩
