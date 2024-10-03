import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,2,3],[3,3,3,3],[1,1,0,0],[0,0,0,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,2,3],[3,3,3,3],[1,1,0,0],[0,0,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,2,3],[3,3,3,3],[1,1,0,0],[0,0,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,2,3],[3,3,3,3],[1,1,0,0],[0,0,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3065,3085] [307,309,310,323,326,329,2644,2646,2652,2659,2662,2665,2672,2687,3052,3058,3061,3068,3071,3078,3081,3089,3093,3097,3253,3255,3256,3258,3259,3261,3262,3264,3265,3266,3306,3309,3312,3316,3319,3322,3326,3330,3334,3338,3458,3459,3461,3464,3467,3509,3512,3515,3519,3522,3525,3529,3533,3537,3541,3659,3662,3664,3665,3668,3672,3712,4269,4270,4284,4287,4314,4316,4318,4340,4341,4360,4584,4599,4602,4631,4655,4675] :=
    ⟨Fin 4, «FinitePoly [[3,2,2,3],[3,3,3,3],[1,1,0,0],[0,0,0,0]]», by decideFin!⟩
