
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,3,3],[3,2,3,3],[2,2,3,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,3,3],[3,2,3,3],[2,2,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,3,3],[3,2,3,3],[2,2,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,3,3],[3,2,3,3],[2,2,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2314, 2368] [211, 231, 1631, 1637, 1644, 1647, 1657, 1718, 1721, 1731, 2266, 2273, 2290, 2300, 2333, 2340, 2443, 2446, 2459, 2466, 2469, 2496, 2506, 2533, 2543, 2646, 2652, 2672, 2699, 2709, 2746, 2778, 3052, 3058, 3068, 3078, 3105, 3115, 3142, 3152, 3255, 3258, 3261, 3268, 3271, 3278, 3306, 3456, 3659, 4070, 4090, 4128, 4131, 4155, 4165, 4269, 4272, 4320, 4606, 4622, 4631] :=
    ⟨Fin 4, «FinitePoly [[0,0,3,3],[3,2,3,3],[2,2,3,3],[0,1,2,3]]», by decideFin!⟩
