
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,3,3,2],[0,0,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,3],[3,3,3,2],[0,0,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,3],[3,3,3,2],[0,0,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,3],[3,3,3,2],[0,0,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [372, 4114] [307, 3664, 3668, 3674, 3678, 3862, 4072, 4076, 4101, 4104, 4269, 4314, 4598, 4606, 4629, 4631, 4635, 4636, 4647, 4684] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,3],[3,3,3,2],[0,0,3,3],[3,3,3,3]]», by decideFin!⟩
