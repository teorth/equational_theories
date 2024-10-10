
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,1,3],[3,3,1,3],[3,3,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,1,3],[3,3,1,3],[3,3,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,1,3],[3,3,1,3],[3,3,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,1,3],[3,3,1,3],[3,3,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4580] [4396, 4399, 4405, 4408, 4433, 4436, 4442, 4445, 4470, 4473, 4479, 4482, 4583, 4598, 4599, 4605, 4606, 4608, 4622, 4629, 4635, 4656, 4658, 4666] :=
    ⟨Fin 4, «FinitePoly [[1,3,1,3],[3,3,1,3],[3,3,3,3],[3,3,3,3]]», by decideFin!⟩
