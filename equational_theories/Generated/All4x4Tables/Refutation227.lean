
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,1,2],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[0,1,2],[0,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[0,1,2],[0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[0,1,2],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2420, 2558] [1631, 1644, 1657, 1721, 2240, 2443, 2459, 2469, 2646, 2699, 2736, 3052, 3068, 3105, 3142, 3253, 3458, 3459, 3461, 3481, 3664, 3674, 3677, 4131, 4155, 4269, 4272, 4314, 4606, 4631] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[0,1,2],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
