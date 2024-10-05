
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3],[2,3,2,3],[2,1,3,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,3],[2,3,2,3],[2,1,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,3],[2,3,2,3],[2,1,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,3],[2,3,2,3],[2,1,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [319, 2420] [326, 1631, 1644, 1657, 1721, 2240, 2443, 2459, 2469, 2530, 2646, 2699, 2736, 3052, 3065, 3068, 3078, 3105, 3115, 3142, 3306, 3459, 3481, 3525, 3529, 3786, 4070, 4084, 4128, 4155, 4362, 4606, 4631, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,3],[2,3,2,3],[2,1,3,3],[0,1,2,3]]», by decideFin!⟩
