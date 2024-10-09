
import equational_theories.Equations.All
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
  ∃ (G : Type) (_ : Magma G), Facts G [2306] [2646, 2662, 2706, 2709, 3058, 3078, 3105, 3142, 3255, 3261, 3467, 3509, 3664, 3684, 3712, 4131, 4165, 4269] :=
    ⟨Fin 4, «FinitePoly [[0,2,2,3],[3,1,2,3],[0,1,0,3],[0,1,2,1]]», by decideFin!⟩
