
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,0,0],[0,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[0,0,0],[0,1,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[0,0,0],[0,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[0,0,0],[0,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2443, 2533, 2709] [203, 1629, 2238, 2459, 3050, 3456, 4065] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[0,0,0],[0,1,1]]», Finite.of_fintype _, by decideFin!⟩
