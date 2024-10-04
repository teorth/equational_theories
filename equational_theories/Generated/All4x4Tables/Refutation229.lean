
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,2,1],[3,3,2,0],[0,1,3,2],[2,2,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,2,1],[3,3,2,0],[0,1,3,2],[2,2,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,2,1],[3,3,2,0],[0,1,3,2],[2,2,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,2,1],[3,3,2,0],[0,1,3,2],[2,2,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [273, 280, 2506, 2530, 3269, 3895] [47, 99, 151, 203, 263, 307, 411, 614, 817, 1020, 1223, 1426, 1629, 1840, 1847, 1884, 1921, 1934, 2035, 2238, 2443, 2446, 2449, 2456, 2493, 2503, 2540, 2644, 2847, 3050, 3319, 3346, 3353, 3456, 3674, 3722, 3725, 3759, 3867, 3877, 3915, 3962, 4065, 4275, 4380, 4598, 4647, 4666] :=
    ⟨Fin 4, «FinitePoly [[3,3,2,1],[3,3,2,0],[0,1,3,2],[2,2,0,3]]», by decideFin!⟩
