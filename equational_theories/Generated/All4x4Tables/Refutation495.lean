
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 0, 1], [1, 2, 0, 1], [3, 2, 0, 2], [3, 2, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 0, 1], [1, 2, 0, 1], [3, 2, 0, 2], [3, 2, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 0, 1], [1, 2, 0, 1], [3, 2, 0, 2], [3, 2, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 0, 1], [1, 2, 0, 1], [3, 2, 0, 2], [3, 2, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [52, 55, 629, 632, 639, 642, 838, 1020, 4606] [8, 49, 99, 375, 411, 616, 619, 622, 825, 848, 856, 1022, 1025, 1028, 1035, 1038, 1045, 1048, 1223, 1629, 1832, 3253, 3456, 3659, 3862, 4269] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 0, 1], [1, 2, 0, 1], [3, 2, 0, 2], [3, 2, 3, 1]]», by decideFin!⟩
