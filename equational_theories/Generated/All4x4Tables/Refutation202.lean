
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 1, 1], [1, 2, 0, 0], [2, 2, 2, 2], [2, 2, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 1, 1], [1, 2, 0, 0], [2, 2, 2, 2], [2, 2, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 1, 1], [1, 2, 0, 0], [2, 2, 2, 2], [2, 2, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 1, 1], [1, 2, 0, 0], [2, 2, 2, 2], [2, 2, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [50, 620, 624, 1028, 1865, 3662, 4341] [40, 48, 49, 52, 53, 55, 56, 62, 63, 65, 66, 72, 73, 75, 99, 359, 411, 616, 617, 619, 629, 630, 632, 633, 639, 640, 642, 643, 666, 667, 669, 670, 676, 677, 679, 680, 703, 704, 706, 707, 713, 714, 716, 1021, 1022, 1023, 1025, 1026, 1029, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1049, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1223, 1629, 1833, 1834, 1837, 1838, 1840, 1841, 1847, 1848, 1850, 1851, 1858, 1860, 1884, 1885, 1887, 1888, 1894, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1931, 1932, 1934, 2441, 3660, 3661, 3665, 3677, 3684, 3685, 3687, 3712, 3725, 3759, 4065, 4380, 4583, 4590, 4591, 4608] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 1, 1], [1, 2, 0, 0], [2, 2, 2, 2], [2, 2, 3, 3]]», by decideFin!⟩
