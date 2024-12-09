
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[2,0,1],[1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[2,0,1],[1,2,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[2,0,1],[1,2,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[2,0,1],[1,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [620, 624] [56, 99, 151, 203, 255, 378, 411, 616, 619, 629, 630, 632, 633, 639, 640, 642, 643, 817, 1021, 1023, 1029, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1049, 1223, 1426, 1629, 1833, 1834, 1837, 1838, 1840, 1841, 1847, 1848, 1851, 1858, 1860, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3664, 3667, 3668, 3712, 3714, 3721, 3722, 3724, 3725, 3862, 4070, 4071, 4074, 4118, 4120, 4121, 4127, 4128, 4130, 4268, 4283, 4284, 4314, 4380, 4584, 4585, 4598, 4599, 4629] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[2,0,1],[1,2,0]]», Finite.of_fintype _, by decideFin!⟩
