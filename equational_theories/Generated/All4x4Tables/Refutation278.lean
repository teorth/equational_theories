import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3],[3,3,1,3],[0,0,0,0],[3,3,0,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,3],[3,3,1,3],[0,0,0,0],[3,3,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,3],[3,3,1,3],[0,0,0,0],[3,3,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,3],[3,3,1,3],[0,0,0,0],[3,3,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4104] [359,361,367,378,3659,3661,3677,3684,3687,3690,3862,3864,3867,3870,3873,3887,4067,4073,4076,4090,4096,4590,4622] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,3],[3,3,1,3],[0,0,0,0],[3,3,0,3]]», by decideFin!⟩
