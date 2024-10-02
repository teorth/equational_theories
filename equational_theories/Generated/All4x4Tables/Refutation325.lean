
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 0, 1], [3, 1, 2, 3], [0, 2, 1, 2], [2, 3, 2, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 0, 1], [3, 1, 2, 3], [0, 2, 1, 2], [2, 3, 2, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 0, 1], [3, 1, 2, 3], [0, 2, 1, 2], [2, 3, 2, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 0, 1], [3, 1, 2, 3], [0, 2, 1, 2], [2, 3, 2, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [11, 429, 440, 639, 658, 820, 1049, 1248, 1835, 1857, 3139, 3286, 3315, 3500, 3700, 3906, 4590] [23, 419, 1038, 1045, 1225, 1226, 1228, 1231, 1238, 1239, 1241, 1251, 1252, 1629, 1850, 2441, 2644, 3058, 3079, 3143, 3152, 3261, 3522, 3719, 3824, 4065] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 0, 1], [3, 1, 2, 3], [0, 2, 1, 2], [2, 3, 2, 1]]», by decideFin!⟩
