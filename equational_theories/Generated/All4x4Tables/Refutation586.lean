
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,3],[3,0,0,1],[3,0,2,2],[2,3,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,3],[3,0,0,1],[3,0,2,2],[2,3,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,1,3],[3,0,0,1],[3,0,2,2],[2,3,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,3],[3,0,0,1],[3,0,2,2],[2,3,3,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [53] [50, 1023, 1028, 1046, 1632, 1637, 1654, 1832, 2441, 2644, 3050, 3464, 3509, 3518, 3522, 3662, 3665, 3712, 4118, 4127, 4270, 4656] :=
    ⟨Fin 4, «FinitePoly [[0,2,1,3],[3,0,0,1],[3,0,2,2],[2,3,3,0]]», Finite.of_fintype _, by decideFin!⟩
