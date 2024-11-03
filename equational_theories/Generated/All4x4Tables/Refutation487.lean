
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
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
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3085] [3052, 3058, 3068, 3253, 3467, 3512, 3537, 4269, 4284, 4599, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,2,2,3],[3,3,3,3],[1,1,0,0],[0,0,0,0]]», Finite.of_fintype _, by decideFin!⟩
