
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,3],[3,3,3,2],[1,0,3,3],[3,0,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,3],[3,3,3,2],[1,0,3,3],[3,0,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,3],[3,3,3,2],[1,0,3,3],[3,0,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,3],[3,3,3,2],[1,0,3,3],[3,0,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3496] [307, 3261, 3306, 3458, 3482, 3522, 3664, 3668, 3674, 3678, 4065] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,3],[3,3,3,2],[1,0,3,3],[3,0,3,3]]», by decideFin!⟩
