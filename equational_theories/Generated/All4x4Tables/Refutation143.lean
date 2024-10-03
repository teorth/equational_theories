import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,1],[3,2,1,3],[1,1,3,2],[2,3,2,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,1],[3,2,1,3],[1,1,3,2],[2,3,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,1],[3,2,1,3],[1,1,3,2],[2,3,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,1],[3,2,1,3],[1,1,3,2],[2,3,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3588,3878,3994] [3253,3259,3308,3319,3331,3462,3522,3534,3659,3880,3915,3997,4065,4068,4083,4118,4158,4200,4273,4332,4380,4386,4435,4446,4458,4588,4647] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,1],[3,2,1,3],[1,1,3,2],[2,3,2,1]]», by decideFin!⟩
