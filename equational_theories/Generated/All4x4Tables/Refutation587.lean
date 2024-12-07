
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,3],[3,0,1,2],[0,3,2,1],[1,2,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,1,0,3],[3,0,1,2],[0,3,2,1],[1,2,3,0]]» : Magma (Fin 4) where
  op := finOpTable "[[2,1,0,3],[3,0,1,2],[0,3,2,1],[1,2,3,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,1,0,3],[3,0,1,2],[0,3,2,1],[1,2,3,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [546, 861, 1061] [419, 427, 436, 466, 477, 511, 614, 835, 842, 870, 883, 906, 1023, 1028, 1036, 1045, 1075, 1086, 1109, 1223, 1426, 1635, 1637, 1645, 1691, 1722, 1840, 1848, 1857, 1887, 1921, 2035, 2238, 2444, 2447, 2459, 2466, 2530, 2543, 2647, 2650, 2652, 2660, 2662, 2669, 2697, 2699, 2706, 2710, 2733, 2744, 2746, 2847, 3105, 3112, 3116, 3143, 3150, 3152, 3253, 3462, 3464, 3481, 3509, 3511, 3545, 3549, 3659, 3862, 4083, 4090, 4158, 4165, 4167, 4270, 4275, 4283, 4320, 4380, 4588, 4590, 4605, 4635] :=
    ⟨Fin 4, «All4x4Tables [[2,1,0,3],[3,0,1,2],[0,3,2,1],[1,2,3,0]]», Finite.of_fintype _, by decideFin!⟩
