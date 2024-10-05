
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,0,1],[1,0,3,2],[1,0,3,2],[2,3,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,0,1],[1,0,3,2],[1,0,3,2],[2,3,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,0,1],[1,0,3,2],[1,0,3,2],[2,3,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,0,1],[1,0,3,2],[1,0,3,2],[2,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [429, 1797, 3388] [99, 151, 427, 817, 1038, 1082, 1109, 1223, 1426, 1631, 1637, 1638, 1644, 1654, 1684, 1694, 1728, 1834, 1837, 1838, 1848, 1857, 1858, 1887, 1894, 1924, 1931, 2035, 2238, 2441, 2644, 2847, 3050, 3255, 3256, 3258, 3259, 3262, 3268, 3281, 3308, 3309, 3316, 3318, 3343, 3456, 3659, 3864, 3865, 3870, 3880, 3890, 3917, 3918, 3924, 3928, 3955, 4065, 4269, 4270, 4272, 4283, 4284, 4291, 4293, 4314, 4380, 4583, 4584, 4590, 4598, 4599, 4608, 4635, 4636] :=
    ⟨Fin 4, «FinitePoly [[2,3,0,1],[1,0,3,2],[1,0,3,2],[2,3,0,1]]», by decideFin!⟩
