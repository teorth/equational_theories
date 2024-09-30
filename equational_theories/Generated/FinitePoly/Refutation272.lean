
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 1 * y**2 + 1 * x + 1 * y + 3 * x * y) % 4' (0, 39, 1831, 1834, 1856, 1860, 1864, 3252, 3255, 3277, 3281, 3285, 3305, 3658, 3661, 3664, 3676, 3683, 3687, 3691, 3699, 3861, 3869, 3877, 3890, 3905, 4269, 4340, 4589, 4621)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + y² + x + y + 3 * x * y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => 2 * x*x + y*y + x + y + 3 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x² + y² + x + y + 3 * x * y % 4» :
  ∃ (G : Type) (_ : Magma G), Facts G [1865, 3286, 3692, 3906, 4341, 4622] [8, 23, 411, 817, 1020, 1426, 1629, 1838, 1840, 1848, 1850, 1887, 1921, 1925, 1934, 2238, 2441, 2644, 3050, 3259, 3261, 3269, 3308, 3315, 3319, 3353, 3456, 3714, 3721, 3725, 3761, 3863, 3864, 3865, 3867, 3868, 3871, 3877, 3880, 3881, 3887, 3888, 3890, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4065, 4275, 4283, 4290, 4585, 4588, 4598] :=
    ⟨Fin 4, «FinitePoly 2 * x² + y² + x + y + 3 * x * y % 4», by decideFin!⟩
