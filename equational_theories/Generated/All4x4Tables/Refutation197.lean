
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[2,3,1,0],[1,2,3,0],[1,3,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[2,3,1,0],[1,2,3,0],[1,3,0,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[2,3,1,0],[1,2,3,0],[1,3,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[2,3,1,0],[1,2,3,0],[1,3,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [420, 501] [47, 99, 151, 211, 221, 255, 413, 416, 417, 419, 426, 429, 436, 437, 440, 466, 477, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4273, 4283, 4284, 4290, 4314, 4380, 4583, 4584, 4585, 4588, 4598, 4599, 4605, 4629] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[2,3,1,0],[1,2,3,0],[1,3,0,2]]», by decideFin!⟩
