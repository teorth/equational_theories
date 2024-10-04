import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,3,3,3],[0,3,1,3],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,3,3,3],[0,3,1,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,3,3,3],[0,3,1,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,3,3,3],[0,3,1,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4450,4457,4467] [4382,4386,4392,4435,4438,4443,4449,4454,4458,4466,4584,4588,4594,4629,4631,4633,4635,4636,4639,4640,4642,4646,4647,4651,4652,4677] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,3,3,3],[0,3,1,3],[3,3,3,3]]», by decideFin!⟩
