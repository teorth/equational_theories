
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,3,0],[1,1,1,1],[2,2,2,2],[3,3,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,3,0],[1,1,1,1],[2,2,2,2],[3,3,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,3,0],[1,1,1,1],[2,2,2,2],[3,3,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,3,0],[1,1,1,1],[2,2,2,2],[3,3,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2045, 2656, 2675, 2883, 3669, 3874] [264, 2037, 2038, 2040, 2041, 2050, 2063, 2064, 2647, 2649, 2652, 2659, 2662, 2670, 2849, 2853, 2855, 2862, 2866, 2872, 3258, 3259, 3261, 3262, 3306, 3308, 3309, 3461, 3462, 3464, 3465, 3509, 3511, 3512, 3661, 3662, 3664, 3665, 3865, 3867, 3870, 4066, 4067, 4074, 4269, 4270, 4283, 4284, 4583, 4599, 4629, 4631] :=
    ⟨Fin 4, «FinitePoly [[0,0,3,0],[1,1,1,1],[2,2,2,2],[3,3,0,3]]», by decideFin!⟩
