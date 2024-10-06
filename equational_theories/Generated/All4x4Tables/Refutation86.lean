
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,1,1],[3,1,3,2],[1,2,0,3],[0,3,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,1,1],[3,1,3,2],[1,2,0,3],[0,3,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,1,1],[3,1,3,2],[1,2,0,3],[0,3,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,1,1],[3,1,3,2],[1,2,0,3],[0,3,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3106, 3149] [47, 105, 107, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3052, 3055, 3058, 3065, 3066, 3068, 3075, 3112, 3115, 3150, 3152, 3253, 3456, 3659, 3862, 4065, 4269, 4272, 4273, 4275, 4284, 4290, 4291, 4320, 4380, 4584, 4587, 4588, 4590, 4599, 4605, 4606, 4635] :=
    ⟨Fin 4, «FinitePoly [[2,0,1,1],[3,1,3,2],[1,2,0,3],[0,3,2,0]]», by decideFin!⟩
