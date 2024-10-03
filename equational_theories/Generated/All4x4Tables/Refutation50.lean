import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,2,3],[3,1,2,3],[0,1,0,3],[0,1,2,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,2,3],[3,1,2,3],[0,1,0,3],[0,1,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,2,3],[3,1,2,3],[0,1,0,3],[0,1,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,2,3],[3,1,2,3],[0,1,0,3],[0,1,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [25,214,2269,2285,2306,2452,2480,2488,2774,3071,3525] [2646,2662,2665,2702,2706,2709,2712,2739,2778,2782,3058,3078,3093,3105,3142,3180,3255,3261,3264,3271,3274,3467,3481,3509,3664,3684,3712,3769,3786,4131,4165,4269,4316] :=
    ⟨Fin 4, «FinitePoly [[0,2,2,3],[3,1,2,3],[0,1,0,3],[0,1,2,1]]», by decideFin!⟩
