
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
  ∃ (G : Type) (_ : Magma G), Facts G [25, 2306, 2774] [2646, 2662, 2702, 2706, 2709, 2739, 2778, 3058, 3078, 3105, 3142, 3255, 3261, 3271, 3467, 3481, 3509, 3664, 3684, 3712, 3769, 4131, 4165, 4269] :=
    ⟨Fin 4, «FinitePoly [[0,2,2,3],[3,1,2,3],[0,1,0,3],[0,1,2,1]]», by decideFin!⟩
