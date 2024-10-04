
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2852, 2878] [255, 2035, 2644, 2855, 2862, 2865, 3253, 3456, 4269, 4284, 4599, 4631] :=
    ⟨Fin 4, «FinitePoly [[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]», by decideFin!⟩
