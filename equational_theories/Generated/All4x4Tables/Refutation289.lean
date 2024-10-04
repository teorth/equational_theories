
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3],[3,3,0,3],[3,0,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,3],[3,3,0,3],[3,0,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,3],[3,3,0,3],[3,0,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,3],[3,3,0,3],[3,0,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3701, 4115] [3671, 3680, 3681, 3695, 3696, 4073, 4081, 4108, 4109, 4598, 4599, 4601, 4605, 4606, 4610, 4611, 4612, 4614, 4615, 4619, 4620, 4629, 4636, 4640, 4642, 4647, 4655, 4656, 4658, 4666, 4673, 4677, 4679] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,3],[3,3,0,3],[3,0,3,3],[3,3,3,3]]», by decideFin!⟩
