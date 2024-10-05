
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3],[2,2,2,1],[0,1,1,1],[0,0,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,3],[2,2,2,1],[0,1,1,1],[0,0,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,3],[2,2,2,1],[0,1,1,1],[0,0,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,3],[2,2,2,1],[0,1,1,1],[0,0,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1849] [1630, 1631, 1632, 1634, 1637, 1834, 1837, 1838, 1840, 2240, 2246, 2253, 2452, 2459, 3254, 3256, 3258, 3316, 3318, 3319, 3460, 3462, 4120, 4121, 4127, 4130, 4131, 4268, 4283, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,3],[2,2,2,1],[0,1,1,1],[0,0,2,0]]», by decideFin!⟩
