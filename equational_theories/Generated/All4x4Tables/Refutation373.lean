import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,3,3],[2,3,3,2],[0,1,2,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,3,3],[2,3,3,2],[0,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,3,3],[2,3,3,2],[0,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,3,3],[2,3,3,2],[0,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [242,246,2263,2273,2310,2327,2355,2364,2389,2402,2420,2425,2430,2554,2623,2791,2836,3115] [307,309,312,323,1647,1657,1721,3065,3197,3253,3255,3258,3261,3264,3268,3271,3274,3278,3288,3306,3458,3461,3467,3519,3664,3674,3677,3694,3749,4070,4131,4269,4272,4316,4351] :=
    ⟨Fin 4, «FinitePoly [[2,1,3,3],[2,3,3,2],[0,1,2,3],[0,1,2,3]]», by decideFin!⟩
