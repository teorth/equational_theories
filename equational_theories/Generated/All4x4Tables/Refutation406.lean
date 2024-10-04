
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,3],[2,2,2,2],[3,3,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,3],[2,2,2,2],[3,3,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,3,3],[2,2,2,2],[3,3,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,3],[2,2,2,2],[3,3,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4659] [4591, 4598, 4599, 4605, 4606, 4608, 4611, 4612, 4614, 4615, 4619, 4620, 4622, 4631, 4640, 4647, 4656, 4666, 4673, 4679, 4684] :=
    ⟨Fin 4, «FinitePoly [[1,2,3,3],[2,2,2,2],[3,3,3,3],[3,3,3,3]]», by decideFin!⟩
