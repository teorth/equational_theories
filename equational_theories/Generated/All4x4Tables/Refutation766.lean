
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,5,3,5,5,5],[2,2,2,2,2,2,6],[3,3,3,3,4,5,3],[6,1,6,6,6,6,6],[1,1,1,3,1,5,1],[6,6,6,6,6,6,6],[0,4,2,4,4,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,5,5,3,5,5,5],[2,2,2,2,2,2,6],[3,3,3,3,4,5,3],[6,1,6,6,6,6,6],[1,1,1,3,1,5,1],[6,6,6,6,6,6,6],[0,4,2,4,4,4,4]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,5,5,3,5,5,5],[2,2,2,2,2,2,6],[3,3,3,3,4,5,3],[6,1,6,6,6,6,6],[1,1,1,3,1,5,1],[6,6,6,6,6,6,6],[0,4,2,4,4,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,5,5,3,5,5,5],[2,2,2,2,2,2,6],[3,3,3,3,4,5,3],[6,1,6,6,6,6,6],[1,1,1,3,1,5,1],[6,6,6,6,6,6,6],[0,4,2,4,4,4,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2886] [255, 2035, 2644, 2849, 2855, 3253, 3456] :=
    ⟨Fin 7, «FinitePoly [[1,5,5,3,5,5,5],[2,2,2,2,2,2,6],[3,3,3,3,4,5,3],[6,1,6,6,6,6,6],[1,1,1,3,1,5,1],[6,6,6,6,6,6,6],[0,4,2,4,4,4,4]]», Finite.of_fintype _, by decideFin!⟩
