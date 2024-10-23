
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,1],[0,2,0],[1,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,1],[0,2,0],[1,1,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[1,0,1],[0,2,0],[1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,1],[0,2,0],[1,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1442, 1444, 1445, 1838, 1848, 1858, 3523, 3526, 4127] [151, 1427, 1428, 1429, 1435, 1629, 1837, 1840, 1847, 1850, 1857, 2050, 2051, 3253, 3462, 3464, 3465, 3509, 3659, 3862, 4068, 4121, 4283, 4284, 4314, 4398, 4472, 4598, 4599] :=
    ⟨Fin 3, «FinitePoly [[1,0,1],[0,2,0],[1,1,1]]», Finite.of_fintype _, by decideFin!⟩
