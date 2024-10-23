
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[1,0,0],[1,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[1,0,0],[1,0,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[1,0,0],[1,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[1,0,0],[1,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2592, 2808, 2964, 2998, 3214] [411, 614, 817, 1020, 1223, 1426, 1632, 1635, 1645, 1647, 1654, 1682, 1684, 1691, 1722, 1832, 2035, 2244, 2254, 2291, 2444, 2447, 2457, 2470, 2534, 2541, 2647, 2650, 2660, 2710, 2853, 2863, 2940, 2947, 3056, 3066, 3079, 3116, 3143, 3150, 3319, 3346, 3353, 3549, 3556, 3725, 3752, 3924, 3951, 4275, 4380, 4588, 4605] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[1,0,0],[1,0,0]]», Finite.of_fintype _, by decideFin!⟩
