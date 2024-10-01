
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 3, 3], [3, 1, 3, 2], [1, 3, 2, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 3, 3], [3, 1, 3, 2], [1, 3, 2, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 3, 3], [3, 1, 3, 2], [1, 3, 2, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 3, 3], [3, 1, 3, 2], [1, 3, 2, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 3, 260, 270, 307, 359, 1228, 1238, 2050, 2087, 2337, 2456, 2530, 2659, 2696, 2899, 2909, 3055, 3112, 3353, 3862, 4070, 4080, 4380] [28, 104, 166, 218, 228, 280, 364, 619, 832, 1035, 1045, 1248, 1478, 1634, 1681, 1691, 1884, 1921, 2124, 2263, 2290, 2327, 2446, 2493, 2503, 2540, 2669, 2706, 2733, 2743, 2919, 2936, 2946, 3075, 3122, 3149, 3461, 3512, 3674, 3749, 3877, 3887, 4090, 4155, 4385, 4587] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 3, 3], [3, 1, 3, 2], [1, 3, 2, 3], [0, 1, 2, 3]]», by decideFin!⟩
