
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,3,3],[2,2,2,2],[1,1,1,1],[0,0,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,3,3],[2,2,2,2],[1,1,1,1],[0,0,0,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,3,3],[2,2,2,2],[1,1,1,1],[0,0,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,3,3],[2,2,2,2],[1,1,1,1],[0,0,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1845, 1863, 1865, 2462, 2472, 4128, 4288] [209, 1426, 1629, 1833, 1838, 1847, 1848, 1850, 1851, 1858, 2239, 2241, 2244, 2247, 2253, 2254, 2257, 2263, 2264, 2266, 2267, 2442, 2444, 2446, 2447, 2449, 2450, 2457, 2460, 2467, 2470, 2644, 3050, 3253, 3456, 3659, 3862, 4071, 4073, 4074, 4118, 4120, 4121, 4127, 4130, 4131, 4269, 4283, 4314, 4584, 4598, 4599, 4605, 4608, 4629, 4658] :=
    ⟨Fin 4, «FinitePoly [[2,3,3,3],[2,2,2,2],[1,1,1,1],[0,0,0,2]]», by decideFin!⟩
