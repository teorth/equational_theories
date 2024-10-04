
import equational_theories.AllEquations
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
  ∃ (G : Type) (_ : Magma G), Facts G [481, 695, 1496, 1710, 1993, 2146, 3008, 3161] [8, 417, 429, 436, 440, 466, 620, 630, 632, 643, 669, 707, 817, 1020, 1223, 1432, 1442, 1481, 1526, 1635, 1684, 1729, 1848, 1894, 1898, 2051, 2090, 2097, 2101, 2238, 2441, 2644, 2863, 2865, 2902, 2909, 2940, 2949, 3058, 3066, 3068, 3112, 3152, 3253, 3286, 3288, 3456, 3712, 3721, 3725, 3759, 3862, 4065, 4098, 4118, 4158, 4165, 4273, 4320, 4386, 4433, 4435, 4480, 4588, 4598] :=
    ⟨Fin 5, «FinitePoly [[0,2,1,4,3],[2,0,3,1,4],[1,4,0,3,2],[4,3,2,0,1],[3,1,4,2,0]]», by decideFin!⟩
