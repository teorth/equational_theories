
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,4,3],[2,0,3,1,4],[1,4,0,3,2],[4,3,2,0,1],[3,1,4,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,4,3],[2,0,3,1,4],[1,4,0,3,2],[4,3,2,0,1],[3,1,4,2,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,1,4,3],[2,0,3,1,4],[1,4,0,3,2],[4,3,2,0,1],[3,1,4,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,4,3],[2,0,3,1,4],[1,4,0,3,2],[4,3,2,0,1],[3,1,4,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1710] [99, 203, 413, 417, 419, 426, 429, 436, 437, 440, 466, 504, 511, 620, 630, 632, 639, 643, 669, 707, 817, 1020, 1223, 1631, 1635, 1644, 1657, 1684, 1721, 1834, 1847, 1848, 1851, 1860, 1894, 2238, 2441, 2644, 2855, 2863, 2865, 2902, 2909, 2940, 2949, 3052, 3058, 3065, 3066, 3068, 3112, 3115, 3116, 3152, 3253, 3456, 3660, 3661, 3664, 3674, 3712, 3721, 3725, 3759, 3862, 4065, 4273, 4283, 4290, 4320, 4398, 4405, 4433, 4435, 4442, 4480, 4588, 4598, 4605, 4635] :=
    ⟨Fin 5, «FinitePoly [[0,2,1,4,3],[2,0,3,1,4],[1,4,0,3,2],[4,3,2,0,1],[3,1,4,2,0]]», by decideFin!⟩
