
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,0,1],[2,0,1,1],[2,3,1,2],[3,3,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,0,1],[2,0,1,1],[2,3,1,2],[3,3,0,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,0,1],[2,0,1,1],[2,3,1,2],[3,3,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,0,1],[2,0,1,1],[2,3,1,2],[3,3,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [52, 55] [616, 632, 642, 845, 1426, 3862, 4067, 4070, 4073, 4608, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,0,0,1],[2,0,1,1],[2,3,1,2],[3,3,0,2]]», by decideFin!⟩
