import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,3,3,3],[1,3,3,0],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[3,3,3,3],[1,3,3,0],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[3,3,3,3],[1,3,3,0],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[3,3,3,3],[1,3,3,0],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4089,4102,4103,4110,4111,4114,4115,4116] [3664,3667,3668,3669,3672,3674,3675,3676,3678,3682,3694,3699,3702,3703,3704,3705,3709,3863,3865,3868,3871,3872,3877,3879,3880,3887,3890,3892,3895,3903,3905,3907,3908,4629] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[3,3,3,3],[1,3,3,0],[3,3,3,3]]», by decideFin!⟩
