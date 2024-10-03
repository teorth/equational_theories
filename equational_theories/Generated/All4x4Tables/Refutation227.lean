import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,1,3],[3,3,3,3],[1,1,0,3],[0,1,2,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,1,3],[3,3,3,3],[1,1,0,3],[0,1,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,1,3],[3,3,3,3],[1,1,0,3],[0,1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,1,3],[3,3,3,3],[1,1,0,3],[0,1,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3052] [307,309,310,323,2644,2646,2652,2659,2662,2665,2672,2687,3058,3065,3068,3071,3078,3093,3253,3255,3256,3258,3259,3261,3262,3264,3265,3266,3306,3456,3458,3459,3461,3464,3467,3509,3519,3522,3525,3529,3537,3659,3662,3664,3665,3668,3672,3712,4269,4270,4314,4316,4318,4341,4584,4631] :=
    ⟨Fin 4, «FinitePoly [[2,2,1,3],[3,3,3,3],[1,1,0,3],[0,1,2,0]]», by decideFin!⟩
