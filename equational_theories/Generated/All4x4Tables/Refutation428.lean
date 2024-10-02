
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 0, 3], [2, 3, 1, 0], [2, 2, 1, 2], [2, 0, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 0, 3], [2, 3, 1, 0], [2, 2, 1, 2], [2, 0, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 0, 3], [2, 3, 1, 0], [2, 2, 1, 2], [2, 0, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 0, 3], [2, 3, 1, 0], [2, 2, 1, 2], [2, 0, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [426] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 359, 412, 413, 414, 416, 417, 419, 420, 427, 429, 430, 436, 437, 439, 440, 463, 464, 466, 467, 473, 474, 476, 477, 500, 501, 503, 504, 510, 511, 513, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 0, 3], [2, 3, 1, 0], [2, 2, 1, 2], [2, 0, 3, 1]]», by decideFin!⟩
