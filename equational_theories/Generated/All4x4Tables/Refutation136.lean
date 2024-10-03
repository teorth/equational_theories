import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,1,3],[3,3,2,2],[0,1,0,0],[0,2,0,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,1,3],[3,3,2,2],[0,1,0,0],[0,2,0,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,1,3],[3,3,2,2],[0,1,0,0],[0,2,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,1,3],[3,3,2,2],[0,1,0,0],[0,2,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2646,2649] [307,309,310,323,326,2035,2652,2659,2662,2665,2669,2672,2687,2847,2862,3253,3255,3256,3258,3259,3261,3262,3264,3265,3266,3306,3319,3456,3458,3459,3461,3464,3467,3509,3519,3522,3525,3529,3537,4269,4270,4314,4316,4318,4341,4584,4631] :=
    ⟨Fin 4, «FinitePoly [[1,1,1,3],[3,3,2,2],[0,1,0,0],[0,2,0,2]]», by decideFin!⟩
