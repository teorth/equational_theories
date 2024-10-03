import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,0,1],[3,3,3,3],[2,2,2,2],[2,1,2,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,0,1],[3,3,3,3],[2,2,2,2],[2,1,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,0,1],[3,3,3,3],[2,2,2,2],[2,1,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,0,1],[3,3,3,3],[2,2,2,2],[2,1,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4066] [4067,4068,4069,4071,4073,4270,4341,4583,4597] :=
    ⟨Fin 4, «FinitePoly [[2,0,0,1],[3,3,3,3],[2,2,2,2],[2,1,2,2]]», by decideFin!⟩
