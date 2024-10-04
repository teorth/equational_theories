
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,3,1],[3,2,2,0],[3,2,2,0],[1,0,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,3,1],[3,2,2,0],[3,2,2,0],[1,0,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,3,1],[3,2,2,0],[3,2,2,0],[1,0,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,3,1],[3,2,2,0],[3,2,2,0],[1,0,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3364, 4216] [3278, 3472, 3878, 4068, 4273, 4275, 4647, 4656] :=
    ⟨Fin 4, «FinitePoly [[0,3,3,1],[3,2,2,0],[3,2,2,0],[1,0,0,3]]», by decideFin!⟩
