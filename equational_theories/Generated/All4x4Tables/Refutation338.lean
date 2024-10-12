
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,1],[3,3,3,0],[3,0,0,0],[2,0,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,1],[3,3,3,0],[3,0,0,0],[2,0,1,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,3,1],[3,3,3,0],[3,0,0,0],[2,0,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,1],[3,3,3,0],[3,0,0,0],[2,0,1,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1833] [151, 203, 1426, 1629, 1834, 1837, 1838, 1840, 1841, 1847, 1848, 1851, 1857, 1858, 1860, 1861, 2238, 2441, 3050, 3253, 3458, 3459, 3461, 3462, 3464, 3465, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 4065, 4268, 4269, 4270, 4283, 4284, 4599] :=
    ⟨Fin 4, «FinitePoly [[1,2,3,1],[3,3,3,0],[3,0,0,0],[2,0,1,2]]», by decideFin!⟩
