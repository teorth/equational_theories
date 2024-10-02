
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 1, 0], [3, 1, 3, 1], [2, 2, 2, 2], [1, 3, 0, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 1, 0], [3, 1, 3, 1], [2, 2, 2, 2], [1, 3, 0, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 1, 0], [3, 1, 3, 1], [2, 2, 2, 2], [1, 3, 0, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 1, 0], [3, 1, 3, 1], [2, 2, 2, 2], [1, 3, 0, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [48, 325, 618, 818, 1022, 1427, 2240, 3317, 3320, 3521, 3714, 4314, 4433] [26, 49, 102, 159, 160, 209, 212, 258, 263, 362, 619, 620, 622, 825, 826, 1026, 1029, 1226, 1229, 1231, 1428, 1451, 1452, 1454, 1455, 1632, 1654, 1655, 1657, 1658, 1850, 1851, 1860, 1861, 2043, 2044, 2060, 2243, 2254, 2257, 2264, 2267, 2449, 2457, 2460, 2467, 2470, 2650, 2653, 2663, 2669, 2672, 2850, 2865, 2875, 3053, 3058, 3066, 3075, 3079, 3459, 3667, 3668, 3868, 3871, 4068, 4073, 4131, 4383, 4585] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 1, 0], [3, 1, 3, 1], [2, 2, 2, 2], [1, 3, 0, 3]]», by decideFin!⟩
