
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,0,1,5,0],[2,5,4,1,2,1],[2,3,5,1,2,2],[2,3,4,5,2,3],[5,3,4,1,5,4],[5,5,5,5,5,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,0,1,5,0],[2,5,4,1,2,1],[2,3,5,1,2,2],[2,3,4,5,2,3],[5,3,4,1,5,4],[5,5,5,5,5,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[2,3,0,1,5,0],[2,5,4,1,2,1],[2,3,5,1,2,2],[2,3,4,5,2,3],[5,3,4,1,5,4],[5,5,5,5,5,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,0,1,5,0],[2,5,4,1,2,1],[2,3,5,1,2,2],[2,3,4,5,2,3],[5,3,4,1,5,4],[5,5,5,5,5,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [433] [818, 833, 836, 1249, 3315, 3864, 3870, 4631] :=
    ⟨Fin 6, «FinitePoly [[2,3,0,1,5,0],[2,5,4,1,2,1],[2,3,5,1,2,2],[2,3,4,5,2,3],[5,3,4,1,5,4],[5,5,5,5,5,5]]», Finite.of_fintype _, by decideFin!⟩
