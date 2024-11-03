
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 1 * y**2 + 0 * x + 0 * y + 1 * x * y) % 3' (0, 39, 42, 3658, 3661, 3664, 3666, 3674, 3676, 3683, 3687, 3691, 3699, 3702, 3711, 3713, 3720, 3724, 3728, 3747, 3751, 3755, 3758, 3760, 3819, 3822, 4269, 4282, 4340, 4357, 4379, 4387, 4397, 4404, 4434, 4441, 4468, 4481, 4496, 4530, 4543, 4589, 4621, 4634, 4676)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + y² + x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => x*x + y*y + x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + y² + x * y % 3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [43, 3703, 3729, 3756, 3820, 3823, 4497] [47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3660, 3661, 3664, 3668, 3674, 3678, 3685, 3687, 3722, 3724, 3737, 3740, 3749, 3751, 3791, 3794, 3862, 4065, 4268, 4269, 4272, 4273, 4275, 4276, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4396, 4399, 4406, 4408, 4433, 4436, 4443, 4445, 4470, 4472, 4473, 4479, 4480, 4583, 4584, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly x² + y² + x * y % 3», Finite.of_fintype _, by decideFin!⟩
