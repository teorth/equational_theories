
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 2, 3], [3, 3, 2, 3], [0, 3, 3, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 2, 3], [3, 3, 2, 3], [0, 3, 3, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 2, 3], [3, 3, 2, 3], [0, 3, 3, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 2, 3], [3, 3, 2, 3], [0, 3, 3, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 319, 368, 3289, 3489, 3502, 3708, 3895, 3904, 3908, 4105, 4109, 4447, 4484] [308, 315, 323, 325, 326, 333, 335, 361, 365, 384, 411, 1020, 1832, 3315, 3319, 3460, 3469, 3479, 3483, 3487, 3491, 3509, 3518, 3522, 3666, 3667, 3675, 3679, 3698, 3864, 3875, 3885, 3888, 3897, 3915, 3928, 4071, 4076, 4083, 4101, 4154, 4362, 4382, 4383, 4385, 4386, 4396, 4398, 4399, 4405, 4406, 4408, 4435, 4436, 4442, 4443, 4472, 4473, 4479, 4480] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 2, 3], [3, 3, 2, 3], [0, 3, 3, 3], [3, 3, 3, 3]]», by decideFin!⟩
