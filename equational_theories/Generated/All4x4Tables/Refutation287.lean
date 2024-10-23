
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,1,2],[1,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[0,1,2],[1,0,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[0,1,2],[1,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[0,1,2],[1,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [690, 947, 1560, 1586, 1797, 2078, 2415, 3495, 3566, 3702, 3790, 4420] [75, 107, 124, 323, 413, 416, 426, 439, 476, 503, 616, 622, 629, 639, 676, 706, 716, 819, 822, 835, 842, 882, 906, 1022, 1028, 1038, 1048, 1082, 1109, 1119, 1225, 1231, 1241, 1251, 1285, 1312, 1322, 1428, 1431, 1441, 1454, 1488, 1515, 1631, 1637, 1644, 1654, 1684, 1694, 1728, 1834, 1837, 1857, 1887, 1894, 1924, 1931, 2037, 2040, 2053, 2060, 2097, 2127, 2134, 3255, 3258, 3268, 3281, 3309, 3316, 3343, 3458, 3464, 3481, 3509, 3519, 3661, 3664, 3677, 3684, 3712, 3725, 3749, 3864, 3870, 3880, 3890, 3918, 3928, 3955, 4067, 4073, 4083, 4093, 4121, 4131, 4158, 4269, 4272, 4284, 4291, 4396, 4406, 4584, 4590, 4599, 4635] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[0,1,2],[1,0,2]]», Finite.of_fintype _, by decideFin!⟩
