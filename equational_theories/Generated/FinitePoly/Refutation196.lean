
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 1 * y**2 + 4 * x + 1 * y + 3 * x * y) % 5' (0, 816, 3252, 3861)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly y² + 4 * x + y + 3 * x * y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => y*y + 4 * x + y + 3 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly y² + 4 * x + y + 3 * x * y % 5» :
  ∃ (G : Type) (_ : Magma G), Facts G [817, 3253, 3862] [411, 818, 819, 820, 822, 823, 825, 826, 832, 833, 835, 836, 842, 843, 845, 846, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1020, 1223, 1629, 1832, 2035, 3261, 3278, 3306, 3319, 3353, 3456, 3659, 3887, 3915, 3962, 4065, 4275, 4283, 4290, 4320, 4380, 4598, 4605, 4635] :=
    ⟨Fin 5, «FinitePoly y² + 4 * x + y + 3 * x * y % 5», by decideFin!⟩
