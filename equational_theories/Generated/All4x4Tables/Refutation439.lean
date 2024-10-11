
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3],[3,2,2,2],[1,3,3,3],[3,3,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,3],[3,2,2,2],[1,3,3,3],[3,3,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,3],[3,2,2,2],[1,3,3,3],[3,3,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,3],[3,2,2,2],[1,3,3,3],[3,3,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3469] [3457, 3464, 4599, 4605, 4608, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,3],[3,2,2,2],[1,3,3,3],[3,3,2,2]]», by decideFin!⟩
