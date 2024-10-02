
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 3, 3], [3, 1, 0, 2], [0, 1, 2, 0], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 3, 3], [3, 1, 0, 2], [0, 1, 2, 0], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 3, 3], [3, 1, 0, 2], [0, 1, 2, 0], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 3, 3], [3, 1, 0, 2], [0, 1, 2, 0], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 3, 228, 270, 307, 359, 1045, 1238, 1921, 2087, 2327, 2337, 2503, 2530, 2540, 2804, 2973, 3887, 4080, 4155, 4380] [28, 104, 166, 208, 218, 260, 280, 364, 619, 832, 1035, 1228, 1248, 1478, 1634, 1681, 1691, 1884, 2050, 2124, 2253, 2263, 2290, 2300, 2456, 2659, 2733, 2852, 2872, 2909, 2946, 3461, 3512, 3674, 4070, 4090, 4192, 4385] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 3, 3], [3, 1, 0, 2], [0, 1, 2, 0], [0, 1, 2, 3]]», by decideFin!⟩
