
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 3, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 3, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 3, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 3, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 4294, 4311, 4312, 4324, 4337, 4346, 4429, 4430, 4466, 4467, 4487, 4489, 4494, 4495, 4499, 4639, 4652, 4661] [40, 307, 359, 3253, 3456, 3659, 3862, 4065, 4271, 4274, 4278, 4287, 4300, 4315, 4328, 4330, 4339, 4340, 4358, 4362, 4364, 4369, 4381, 4388, 4396, 4408, 4433, 4445, 4470, 4482, 4518, 4521, 4536, 4538, 4547, 4554, 4555, 4557, 4560, 4563, 4565, 4569, 4570, 4583, 4590, 4598, 4599, 4605, 4606, 4608, 4677, 4683] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 3, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 3, 3]]», by decideFin!⟩
