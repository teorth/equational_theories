
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,4,1],[2,3,1,0,4],[3,1,4,2,0],[4,0,2,1,3],[1,4,0,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,4,1],[2,3,1,0,4],[3,1,4,2,0],[4,0,2,1,3],[1,4,0,3,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,3,4,1],[2,3,1,0,4],[3,1,4,2,0],[4,0,2,1,3],[1,4,0,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,4,1],[2,3,1,0,4],[3,1,4,2,0],[4,0,2,1,3],[1,4,0,3,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [623, 775, 2946] [47, 99, 203, 255, 413, 417, 419, 426, 436, 440, 466, 477, 504, 620, 622, 630, 643, 669, 676, 680, 817, 1028, 1036, 1038, 1045, 1049, 1075, 1086, 1241, 1248, 1252, 1276, 1285, 1426, 1629, 1832, 2035, 2244, 2246, 2256, 2291, 2340, 2449, 2457, 2459, 2466, 2496, 2541, 2543, 2644, 2853, 2863, 2872, 2902, 2909, 2947, 2949, 3058, 3066, 3075, 3112, 3143, 3150, 3152, 3253, 3456, 3659, 3862, 4065, 4269, 4270, 4272, 4273, 4275, 4290, 4320, 4396, 4433, 4473, 4480, 4583, 4584, 4585, 4588, 4590, 4598, 4605] :=
    ⟨Fin 5, «FinitePoly [[0,2,3,4,1],[2,3,1,0,4],[3,1,4,2,0],[4,0,2,1,3],[1,4,0,3,2]]», Finite.of_fintype _, by decideFin!⟩
