
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,0,1],[3,2,1,0],[3,2,1,0],[3,2,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,0,1],[3,2,1,0],[3,2,1,0],[3,2,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,0,1],[3,2,1,0],[3,2,1,0],[3,2,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,0,1],[3,2,1,0],[3,2,1,0],[3,2,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1975, 3901, 3972] [99, 159, 359, 411, 622, 632, 639, 825, 835, 842, 872, 879, 906, 1020, 1223, 1426, 1629, 1834, 1837, 1840, 1857, 1860, 1897, 1921, 1924, 2037, 2040, 2043, 2050, 2060, 2063, 2087, 2124, 2127, 2238, 2459, 2466, 2503, 2530, 2543, 2652, 2662, 2669, 2699, 2746, 2847, 3068, 3105, 3112, 3152, 3253, 3456, 3659, 3864, 3870, 3877, 3915, 3918, 3925, 3928, 3955, 4067, 4070, 4083, 4090, 4118, 4121, 4128, 4131, 4155, 4158, 4165, 4269, 4272, 4275, 4284, 4291, 4320, 4380, 4584, 4587, 4590, 4599, 4635] :=
    ⟨Fin 4, «FinitePoly [[3,1,0,1],[3,2,1,0],[3,2,1,0],[3,2,1,0]]», by decideFin!⟩
