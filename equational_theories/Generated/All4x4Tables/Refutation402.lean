
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 1, 0, 1], [2, 3, 1, 1], [2, 3, 0, 2], [0, 3, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 1, 0, 1], [2, 3, 1, 1], [2, 3, 0, 2], [0, 3, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 1, 0, 1], [2, 3, 1, 1], [2, 3, 0, 2], [0, 3, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 1, 0, 1], [2, 3, 1, 1], [2, 3, 0, 2], [0, 3, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [8, 361, 1228, 1687, 1894, 2040, 3877, 4584] [104, 156, 364, 375, 1038, 1055, 1225, 1231, 1238, 1248, 1634, 1644, 1647, 1654, 1691, 1837, 1847, 1857, 1884, 1921, 3306, 3343, 3353, 3880, 3897, 4067, 4080, 4090, 4118, 4128, 4155, 4291, 4587, 4635] :=
    ⟨Fin 4, «FinitePoly [[2, 1, 0, 1], [2, 3, 1, 1], [2, 3, 0, 2], [0, 3, 0, 1]]», by decideFin!⟩
