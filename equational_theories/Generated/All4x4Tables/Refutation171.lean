
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[0,0,1],[0,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1],[0,0,1],[0,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,2,1],[0,0,1],[0,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1],[0,0,1],[0,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1041, 1063, 1664, 1672, 1738, 3264, 3285, 3316] [105, 108, 151, 411, 817, 1023, 1036, 1039, 1045, 1046, 1049, 1075, 1085, 1109, 1112, 1224, 1225, 1229, 1239, 1242, 1249, 1251, 1252, 1278, 1285, 1288, 1315, 1322, 1426, 1631, 1681, 1684, 1691, 1694, 1721, 1832, 2035, 3281, 3306, 3309, 3315, 3318, 3319, 3343, 3456, 3660, 3661, 3721, 3724, 3725, 3862, 4065, 4269, 4284, 4314, 4583, 4584, 4598, 4606] :=
    ⟨Fin 3, «FinitePoly [[0,2,1],[0,0,1],[0,2,0]]», Finite.of_fintype _, by decideFin!⟩
