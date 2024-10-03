import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,3,3,3],[2,1,3,3],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,3],[3,3,3,3],[2,1,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,3],[3,3,3,3],[2,1,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,3],[3,3,3,3],[2,1,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3477,3486,3493,3499,3501,3502,3505,3882,3885,3886,3889,3892,3896,3899,3900,3904,3907,3908,3911,3912,3913] [3461,3463,3467,3475,3476,3478,3492,3495,3496,3498,3504,3667,3675,3703] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,3],[3,3,3,3],[2,1,3,3],[3,3,3,3]]», by decideFin!⟩
