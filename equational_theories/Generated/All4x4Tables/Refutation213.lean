
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,3,1],[3,0,3,2],[3,3,1,0],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,3,1],[3,0,3,2],[3,3,1,0],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,3,1],[3,0,3,2],[3,3,1,0],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,3,1],[3,0,3,2],[3,3,1,0],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1641, 4392] [151, 203, 1427, 1428, 1429, 1431, 1434, 1441, 1445, 1451, 1454, 1632, 1637, 1644, 1648, 1654, 1655, 1657, 1832, 2238, 2441, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4283, 4284, 4314, 4396, 4399, 4435, 4470, 4473, 4583, 4585, 4587, 4590, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4658] :=
    ⟨Fin 4, «FinitePoly [[2,3,3,1],[3,0,3,2],[3,3,1,0],[3,3,3,3]]», by decideFin!⟩
