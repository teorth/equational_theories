
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,1,1],[3,1,1,1],[1,3,3,3],[1,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,1,1],[3,1,1,1],[1,3,3,3],[1,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,1,1],[3,1,1,1],[1,3,3,3],[1,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,1,1],[3,1,1,1],[1,3,3,3],[1,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4521] [4381, 4396, 4398, 4433, 4435, 4470, 4472, 4507, 4508, 4510, 4512, 4514, 4515, 4583, 4599, 4603, 4629, 4631] :=
    ⟨Fin 4, «FinitePoly [[2,1,1,1],[3,1,1,1],[1,3,3,3],[1,3,3,3]]», by decideFin!⟩
