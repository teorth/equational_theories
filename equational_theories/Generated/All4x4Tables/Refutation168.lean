
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 2, 3], [1, 0, 2, 3], [3, 1, 0, 2], [2, 1, 3, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 2, 3], [1, 0, 2, 3], [3, 1, 0, 2], [2, 1, 3, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 2, 3], [1, 0, 2, 3], [3, 1, 0, 2], [2, 1, 3, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 2, 3], [1, 0, 2, 3], [3, 1, 0, 2], [2, 1, 3, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [31, 1137, 1865, 1996, 3105, 3500, 4098] [26, 411, 1023, 1036, 1038, 1045, 1049, 1073, 1075, 1086, 1113, 1632, 1645, 1647, 1654, 1658, 1684, 1691, 1722, 1838, 1840, 1894, 1898, 1921, 1925, 2238, 2444, 2449, 2457, 2470, 2534, 2647, 2697, 2699, 2710, 2737, 2847, 3053, 3066, 3075, 3079, 3143, 3459, 3481, 3518, 3549, 3556, 3748, 3752, 4073, 4081, 4127, 4273, 4320, 4380, 4585, 4605] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 2, 3], [1, 0, 2, 3], [3, 1, 0, 2], [2, 1, 3, 0]]», by decideFin!⟩
