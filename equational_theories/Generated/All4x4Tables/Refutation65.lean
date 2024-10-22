
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,3],[3,1,2,3],[3,1,2,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,3],[3,1,2,3],[3,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,3],[3,1,2,3],[3,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,3],[3,1,2,3],[3,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2259, 2296] [211, 2266, 2303, 2330, 2449, 2459, 2469, 2662, 2699, 2736, 3052, 3068, 3078, 3255, 3306, 3458, 3464, 3529, 3664, 3684, 3712, 4128, 4269, 4631] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,3],[3,1,2,3],[3,1,2,3],[0,1,2,3]]», Finite.of_fintype _, by decideFin!⟩
