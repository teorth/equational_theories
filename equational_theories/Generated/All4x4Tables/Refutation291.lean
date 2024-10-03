import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,3],[3,3,0,3],[3,1,3,3],[3,0,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,3,3],[3,3,0,3],[3,1,3,3],[3,0,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,3,3],[3,3,0,3],[3,1,3,3],[3,0,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,3,3],[3,3,0,3],[3,1,3,3],[3,0,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3473,3476,3477,3479,3480,3483,3486,3487,3490,3493,3494,3495,3498,3499,3501,3502,3503,3505,3506,3507] [3660,3661,3663,3666,3667,3669,3670,3671,3673,3675,3676,3679,3680,3681,3683,3685,3686,3687,3689,3690,3691,3693,3695,3696,3697,3698,3701,3702,3703,3705,3706,3707,3708,3710,4070,4080,4100] :=
    ⟨Fin 4, «FinitePoly [[3,0,3,3],[3,3,0,3],[3,1,3,3],[3,0,3,3]]», by decideFin!⟩
