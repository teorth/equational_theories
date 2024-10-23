
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,4,3,0],[4,3,2,0,1],[3,1,0,4,2],[0,4,1,2,3],[2,0,3,1,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,4,3,0],[4,3,2,0,1],[3,1,0,4,2],[0,4,1,2,3],[2,0,3,1,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,4,3,0],[4,3,2,0,1],[3,1,0,4,2],[0,4,1,2,3],[2,0,3,1,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,4,3,0],[4,3,2,0,1],[3,1,0,4,2],[0,4,1,2,3],[2,0,3,1,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [452, 467, 2127, 2707, 2743, 2903, 2937, 2939] [47, 105, 107, 151, 203, 255, 413, 416, 419, 420, 426, 436, 437, 466, 477, 501, 503, 504, 511, 614, 817, 1020, 1223, 1426, 1629, 1832, 2036, 2037, 2038, 2040, 2041, 2044, 2050, 2060, 2063, 2128, 2238, 2441, 2670, 2672, 2700, 2709, 2710, 2736, 2853, 2863, 2875, 2902, 2912, 2940, 2947, 3050, 3253, 3456, 3659, 3862, 4065, 4275, 4283, 4293, 4380, 4585, 4588, 4608, 4635] :=
    ⟨Fin 5, «FinitePoly [[1,2,4,3,0],[4,3,2,0,1],[3,1,0,4,2],[0,4,1,2,3],[2,0,3,1,4]]», Finite.of_fintype _, by decideFin!⟩
