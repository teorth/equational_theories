
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4301, 4410, 4429, 4430, 4640] [43, 307, 359, 3253, 3456, 3659, 3862, 4065, 4100, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4154, 4155, 4157, 4158, 4164, 4165, 4167, 4270, 4272, 4284, 4290, 4314, 4320, 4343, 4358, 4384, 4391, 4400, 4402, 4407, 4411, 4416, 4419, 4437, 4439, 4444, 4448, 4453, 4456, 4470, 4472, 4473, 4479, 4480, 4482, 4586, 4593, 4602, 4615, 4630, 4673, 4677] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,3,3,3],[3,3,1,3],[3,3,3,3]]», by decideFin!⟩
