
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[0,2,0],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1],[0,2,0],[0,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,2,1],[0,2,0],[0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1],[0,2,0],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [166, 1867, 1975, 3883, 3897, 3901] [99, 159, 359, 411, 1020, 1223, 1629, 1834, 1840, 1850, 1860, 1897, 1921, 1924, 2037, 2040, 2043, 2060, 2063, 2127, 3253, 3659, 3865, 3870, 3893, 3915, 3918, 3925, 3928, 3955, 3962, 4070, 4090, 4118, 4121, 4128, 4155, 4158, 4165, 4272, 4275, 4284, 4291, 4314, 4320, 4584, 4587, 4590, 4599, 4635] :=
    ⟨Fin 3, «FinitePoly [[0,2,1],[0,2,0],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
