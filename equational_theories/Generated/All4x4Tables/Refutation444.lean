
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 1, 3], [3, 0, 1, 0], [3, 3, 0, 1], [1, 0, 3, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 1, 3], [3, 0, 1, 0], [3, 3, 0, 1], [1, 0, 3, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 1, 3], [3, 0, 1, 0], [3, 3, 0, 1], [1, 0, 3, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 1, 3], [3, 0, 1, 0], [3, 3, 0, 1], [1, 0, 3, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 3703, 3756, 3820] [2, 3, 8, 23, 38, 39, 43, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3660, 3661, 3664, 3668, 3674, 3678, 3685, 3687, 3714, 3721, 3722, 3724, 3725, 3749, 3751, 3761, 3794, 3862, 4065, 4268, 4269, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 1, 3], [3, 0, 1, 0], [3, 3, 0, 1], [1, 0, 3, 0]]», by decideFin!⟩
