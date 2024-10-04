
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,3,3],[3,3,0,3],[0,0,3,0],[0,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,3,3],[3,3,0,3],[0,0,3,0],[0,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,3,3],[3,3,0,3],[0,0,3,0],[0,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,3,3],[3,3,0,3],[0,0,3,0],[0,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3837] [3253, 3456, 3661, 3667, 3677, 3715, 3725, 3887, 3921, 3928, 3935, 4067, 4070, 4073, 4080, 4090, 4100, 4121, 4134, 4138, 4146, 4165, 4192, 4269, 4272, 4284, 4291, 4320, 4396, 4445, 4470, 4473, 4599, 4606, 4622, 4631, 4666] :=
    ⟨Fin 4, «FinitePoly [[0,0,3,3],[3,3,0,3],[0,0,3,0],[0,3,3,3]]», by decideFin!⟩
