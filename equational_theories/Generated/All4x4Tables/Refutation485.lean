
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 0, 1], [1, 1, 1, 1], [2, 2, 3, 1], [0, 3, 3, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 0, 1], [1, 1, 1, 1], [2, 2, 3, 1], [0, 3, 3, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 0, 1], [1, 1, 1, 1], [2, 2, 3, 1], [0, 3, 3, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 0, 1], [1, 1, 1, 1], [2, 2, 3, 1], [0, 3, 3, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [836, 1048, 1049] [99, 818, 819, 820, 822, 823, 825, 826, 832, 833, 835, 842, 843, 845, 846, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1038, 1223, 3862] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 0, 1], [1, 1, 1, 1], [2, 2, 3, 1], [0, 3, 3, 0]]», by decideFin!⟩
