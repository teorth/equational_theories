
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[1,0,0],[2,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[1,0,0],[2,1,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[1,0,0],[2,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[1,0,0],[2,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [835, 847, 1052, 4093] [105, 107, 359, 411, 819, 832, 833, 836, 842, 843, 1023, 1028, 1035, 1036, 1038, 1039, 1045, 1048, 1223, 1832, 3255, 3256, 3278, 3279, 3306, 3315, 3316, 3318, 3319, 3659, 3862, 4066, 4067, 4068, 4070, 4071, 4083, 4084, 4090, 4091, 4131, 4269, 4270, 4293, 4314, 4583, 4588, 4598, 4606, 4622, 4631] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[1,0,0],[2,1,1]]», Finite.of_fintype _, by decideFin!⟩
