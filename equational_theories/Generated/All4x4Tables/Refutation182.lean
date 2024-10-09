
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,3,3],[3,3,2,2],[1,1,0,0],[0,0,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,3,3],[3,3,2,2],[1,1,0,0],[0,0,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,3,3],[3,3,2,2],[1,1,0,0],[0,0,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,3,3],[3,3,2,2],[1,1,0,0],[0,0,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [161, 3083, 3091] [211, 1431, 1434, 1435, 1441, 1445, 1629, 1832, 2035, 2244, 2247, 2253, 2256, 2266, 2441, 3052, 3055, 3065, 3069, 3076, 3253, 3461, 3462, 3464, 3465, 3509, 3511, 3512, 3659, 3862, 4065, 4269, 4270, 4283, 4284, 4380, 4583, 4584, 4599, 4629, 4636] :=
    ⟨Fin 4, «FinitePoly [[2,2,3,3],[3,3,2,2],[1,1,0,0],[0,0,1,1]]», by decideFin!⟩
