
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,0,3],[2,2,1,0],[2,2,0,3],[2,3,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,0,3],[2,2,1,0],[2,2,0,3],[2,3,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,0,3],[2,2,1,0],[2,2,0,3],[2,3,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,0,3],[2,2,1,0],[2,2,0,3],[2,3,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [416, 4131, 4590] [56, 99, 151, 261, 264, 359, 413, 417, 419, 420, 426, 429, 436, 437, 440, 615, 620, 623, 630, 633, 640, 643, 826, 833, 836, 843, 846, 1020, 1223, 1629, 1832, 2035, 2647, 2650, 2660, 2670, 2853, 2856, 2863, 2866, 2873, 3253, 3457, 3459, 3465, 3521, 3659, 3862, 4066, 4067, 4068, 4070, 4071, 4073, 4118, 4120, 4121, 4128, 4268, 4269, 4270, 4283, 4284, 4314, 4398, 4433, 4436, 4472, 4583, 4584, 4585, 4598, 4599, 4606, 4629] :=
    ⟨Fin 4, «FinitePoly [[2,2,0,3],[2,2,1,0],[2,2,0,3],[2,3,1,0]]», by decideFin!⟩
