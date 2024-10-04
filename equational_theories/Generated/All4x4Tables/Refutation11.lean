
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[1,2,0],[2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[1,2,0],[2,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[1,2,0],[2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[1,2,0],[2,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [43, 56, 66, 73, 75, 108, 118, 125, 127, 160, 170, 177, 179, 212, 222, 229, 231, 264, 274, 281, 283, 4276, 4362, 4364, 4369, 4512, 4515, 4525, 4591, 4673, 4679, 4684] [50, 53, 55, 63, 65, 72, 102, 105, 107, 115, 117, 124, 154, 157, 159, 167, 169, 176, 206, 209, 211, 219, 221, 228, 258, 261, 263, 271, 273, 280, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4284, 4291, 4293, 4314, 4321, 4343, 4399, 4406, 4408, 4436, 4443, 4445, 4470, 4472, 4479, 4583, 4584, 4585, 4587, 4588, 4590, 4599, 4606, 4608, 4629, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[1,2,0],[2,0,1]]», by decideFin!⟩
