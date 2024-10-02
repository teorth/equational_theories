
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 2, 3], [1, 0, 0, 0], [2, 2, 0, 0], [3, 2, 0, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 2, 3], [1, 0, 0, 0], [2, 2, 0, 0], [3, 2, 0, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 2, 3], [1, 0, 0, 0], [2, 2, 0, 0], [3, 2, 0, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 2, 3], [1, 0, 0, 0], [2, 2, 0, 0], [3, 2, 0, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [647, 1256, 1523, 2132, 3489, 4098, 4398, 4497] [26, 417, 427, 1023, 1038, 1231, 1239, 1442, 1451, 1455, 1632, 1647, 1654, 1658, 1838, 1850, 2051, 2060, 2064, 2254, 2267, 2457, 2470, 2660, 2673, 2850, 2876, 3105, 3306, 3511, 3518, 3917, 4073, 4127, 4383, 4473] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 2, 3], [1, 0, 0, 0], [2, 2, 0, 0], [3, 2, 0, 0]]», by decideFin!⟩
