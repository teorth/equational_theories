
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 4 * y**2 + 2 * x + 1 * y + 0 * x * y) % 5' (0, 816, 4607)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + 4 * y² + 2 * x + y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => x*x + 4 * y*y + 2 * x + y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + 4 * y² + 2 * x + y % 5» :
  ∃ (G : Type) (_ : Magma G), Facts G [817, 4608] [47, 99, 151, 203, 255, 411, 614, 818, 819, 820, 822, 823, 825, 826, 832, 833, 835, 836, 842, 843, 845, 846, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4629, 4635, 4636, 4658] :=
    ⟨Fin 5, «FinitePoly x² + 4 * y² + 2 * x + y % 5», by decideFin!⟩
