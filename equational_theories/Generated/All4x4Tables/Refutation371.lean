
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0,1],[3,1,1,2],[3,3,3,2],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0,1],[3,1,1,2],[3,3,3,2],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,0,1],[3,1,1,2],[3,3,3,2],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0,1],[3,1,1,2],[3,3,3,2],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1885] [40, 414, 473, 477, 513, 872, 1632, 1654, 1682, 1838, 1861, 1925, 2449, 2470, 3075, 3079, 3459, 3518, 3558, 4073, 4127, 4656] :=
    ⟨Fin 4, «FinitePoly [[0,0,0,1],[3,1,1,2],[3,3,3,2],[0,1,2,3]]», by decideFin!⟩
