
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,1,3],[3,3,2,0],[3,3,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,1,3],[3,3,2,0],[3,3,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,1,3],[3,3,2,0],[3,3,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,1,3],[3,3,2,0],[3,3,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4107, 4111, 4113] [3862, 4078, 4088, 4100, 4598, 4599, 4629, 4655, 4656, 4673] :=
    ⟨Fin 4, «FinitePoly [[3,2,1,3],[3,3,2,0],[3,3,3,3],[3,3,3,3]]», by decideFin!⟩
