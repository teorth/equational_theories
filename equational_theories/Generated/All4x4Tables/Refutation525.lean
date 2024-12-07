
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[2,3,0,1],[3,2,1,0],[1,0,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,1,2,3],[2,3,0,1],[3,2,1,0],[1,0,3,2]]» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[2,3,0,1],[3,2,1,0],[1,0,3,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,1,2,3],[2,3,0,1],[3,2,1,0],[1,0,3,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [271, 283, 1029, 1039, 1083, 1110, 1638, 1719, 1851, 1858, 1888, 1895, 3871, 3881, 3927, 3954] [47, 99, 151, 203, 261, 307, 437, 504, 614, 817, 1023, 1046, 1109, 1113, 1223, 1426, 1631, 1632, 1634, 1637, 1654, 1838, 1848, 1860, 1861, 1925, 2035, 2238, 2441, 2644, 2847, 3050, 3279, 3345, 3456, 3659, 3864, 3867, 3870, 3878, 3888, 4065, 4269, 4270, 4283, 4284, 4314, 4321, 4343, 4380, 4583, 4584, 4585, 4588, 4590, 4598, 4599] :=
    ⟨Fin 4, «All4x4Tables [[0,1,2,3],[2,3,0,1],[3,2,1,0],[1,0,3,2]]», Finite.of_fintype _, by decideFin!⟩
