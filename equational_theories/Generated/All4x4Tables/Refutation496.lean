
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,1,1],[3,0,3,2],[2,2,2,2],[2,0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,1,1],[3,0,3,2],[2,2,2,2],[2,0,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,1,1],[3,0,3,2],[2,2,2,2],[2,0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,1,1],[3,0,3,2],[2,2,2,2],[2,0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1431, 1638] [3253, 3462, 3465, 3518, 3521, 4065, 4314, 4599] :=
    ⟨Fin 4, «FinitePoly [[3,2,1,1],[3,0,3,2],[2,2,2,2],[2,0,0,1]]», Finite.of_fintype _, by decideFin!⟩
