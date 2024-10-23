
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0,0],[2,1,1,1],[3,2,2,2],[1,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0,0],[2,1,1,1],[3,2,2,2],[1,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,0,0],[2,1,1,1],[3,2,2,2],[1,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0,0],[2,1,1,1],[3,2,2,2],[1,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1237, 2887, 3069, 3076, 3716, 3930] [261, 263, 2037, 2038, 2040, 2041, 2043, 2044, 2050, 2053, 2054, 2060, 2061, 2647, 2649, 2650, 2652, 2659, 2660, 2662, 2669, 2672, 2849, 2853, 2855, 2856, 2862, 2863, 2865, 2872, 2873, 2875, 3258, 3259, 3261, 3262, 3306, 3308, 3309, 3461, 3462, 3464, 3465, 3509, 3511, 3512, 4131, 4269, 4270, 4283, 4284, 4597, 4599, 4629, 4631, 4656] :=
    ⟨Fin 4, «FinitePoly [[0,0,0,0],[2,1,1,1],[3,2,2,2],[1,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
