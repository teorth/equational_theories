import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,1],[3,1,3,0],[2,2,2,2],[1,0,0,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,1],[3,1,3,0],[2,2,2,2],[1,0,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,1],[3,1,3,0],[2,2,2,2],[1,0,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,1],[3,1,3,0],[2,2,2,2],[1,0,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2244] [3079,3083,3094,3259,3261,3308,3331,3334,3459,3526,4068,4073,4131,4135,4146,4283,4358,4585,4656] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,1],[3,1,3,0],[2,2,2,2],[1,0,0,3]]», by decideFin!⟩
