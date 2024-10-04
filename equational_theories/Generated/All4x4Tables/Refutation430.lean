import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,2,3],[3,3,2,3],[1,3,2,3],[3,3,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,2,3],[3,3,2,3],[1,3,2,3],[3,3,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,2,3],[3,3,2,3],[1,3,2,3],[3,3,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,2,3],[3,3,2,3],[1,3,2,3],[3,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [318,3274,3284,3292,3296,3300,3477,3487,3499,3503,3690,3698,3706,4569] [4382,4388,4391,4396,4402,4406,4412,4416,4424,4428,4435,4438,4445,4448,4456,4460,4464,4470,4476,4480,4486,4490,4498,4502,4508,4512,4520,4525,4529,4537,4542,4546,4554,4559,4564,4574,4579,4584,4590,4593,4599,4602,4611,4619,4622,4625,4631,4635,4638,4642,4649,4655,4663,4669,4675,4677,4682,4693] :=
    ⟨Fin 4, «FinitePoly [[3,3,2,3],[3,3,2,3],[1,3,2,3],[3,3,2,3]]», by decideFin!⟩
