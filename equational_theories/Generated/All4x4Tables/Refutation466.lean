
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 0, 1], [3, 0, 1, 0], [2, 2, 2, 2], [1, 2, 3, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 0, 1], [3, 0, 1, 0], [2, 2, 2, 2], [1, 2, 3, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 0, 1], [3, 0, 1, 0], [2, 2, 2, 2], [1, 2, 3, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 0, 1], [3, 0, 1, 0], [2, 2, 2, 2], [1, 2, 3, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [108, 1052, 1253, 1832, 3253, 4591] [105, 107, 117, 127, 818, 819, 820, 822, 823, 825, 826, 832, 833, 835, 836, 842, 843, 845, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1021, 1023, 1025, 1026, 1028, 1029, 1035, 1036, 1038, 1039, 1048, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1225, 1226, 1228, 1229, 1231, 1232, 1238, 1239, 1242, 1248, 1249, 1275, 1276, 1278, 1279, 1285, 1286, 1288, 1289, 1312, 1313, 1315, 1316, 1322, 1323, 1325, 1833, 1834, 1835, 1837, 1838, 1840, 1841, 1847, 1848, 1850, 1851, 1857, 1858, 1860, 1861, 1884, 1885, 1887, 1888, 1894, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1931, 1932, 1934, 3255, 3256, 3315, 3319] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 0, 1], [3, 0, 1, 0], [2, 2, 2, 2], [1, 2, 3, 2]]», by decideFin!⟩
