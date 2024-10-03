import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,3,1,3],[1,1,1,1],[3,3,0,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,3],[3,3,1,3],[1,1,1,1],[3,3,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,3],[3,3,1,3],[1,1,1,1],[3,3,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,3],[3,3,1,3],[1,1,1,1],[3,3,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4523,4540,4557] [4388,4391,4408,4411,4419,4423,4427,4445,4448,4456,4460,4464,4482,4485,4493,4497,4501,4527,4531,4535,4544,4548,4552,4562,4567,4572,4577,4590,4593,4599,4602,4606,4611,4615,4619,4622,4625,4638,4645,4649,4655,4663,4669,4675,4682,4689,4693] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,3],[3,3,1,3],[1,1,1,1],[3,3,0,3]]», by decideFin!⟩
