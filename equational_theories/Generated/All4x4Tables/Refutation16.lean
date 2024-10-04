
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,2,3],[3,2,3,2],[1,0,1,0],[0,1,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,2,3],[3,2,3,2],[1,0,1,0],[0,1,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,2,3],[3,2,3,2],[1,0,1,0],[0,1,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,2,3],[3,2,3,2],[1,0,1,0],[0,1,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1662, 1670, 1673, 2474, 2482, 2485, 3083, 3091, 3094, 3334, 4656] [203, 307, 1426, 1832, 2238, 2443, 2456, 2469, 2644, 3052, 3065, 3078, 3255, 3256, 3259, 3308, 3315, 3456, 3659, 3862, 4065, 4269, 4270, 4283, 4314, 4321, 4343, 4380, 4606, 4631, 4658] :=
    ⟨Fin 4, «FinitePoly [[2,3,2,3],[3,2,3,2],[1,0,1,0],[0,1,0,1]]», by decideFin!⟩
