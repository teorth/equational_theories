
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,1,3],[3,1,3,0],[2,2,2,2],[0,3,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,1,3],[3,1,3,0],[2,2,2,2],[0,3,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,1,3],[3,1,3,0],[2,2,2,2],[0,3,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,1,3],[3,1,3,0],[2,2,2,2],[0,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1645, 2447] [1632, 1635, 1637, 1658, 1670, 2449, 2457, 2459, 2470, 3050, 3075, 3094, 4656] :=
    ⟨Fin 4, «FinitePoly [[1,0,1,3],[3,1,3,0],[2,2,2,2],[0,3,0,1]]», by decideFin!⟩
