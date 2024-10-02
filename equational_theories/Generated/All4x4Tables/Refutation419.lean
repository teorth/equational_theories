
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 1, 3], [3, 3, 0, 3], [0, 1, 3, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 1, 3], [3, 3, 0, 3], [0, 1, 3, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 1, 3], [3, 3, 0, 3], [0, 1, 3, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 1, 3], [3, 3, 0, 3], [0, 1, 3, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3294, 3497, 3710, 3903, 4106, 4544] [43, 308, 309, 313, 315, 323, 325, 326, 332, 333, 335, 336, 378, 3255, 3279, 3306, 3315, 3319, 3461, 3475, 3509, 3522, 3864, 3888, 4070, 4084, 4131, 4283, 4383, 4386, 4396, 4398, 4433, 4442, 4473, 4480, 4635] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 1, 3], [3, 3, 0, 3], [0, 1, 3, 3], [3, 3, 3, 3]]», by decideFin!⟩
