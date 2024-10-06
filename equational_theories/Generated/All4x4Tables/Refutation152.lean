
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[2,3,2,3],[2,1,2,1],[2,3,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,2,1],[2,3,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[2,3,2,3],[2,1,2,1],[2,3,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,2,1],[2,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3541] [3253, 3459, 3511, 3661, 3664, 3667, 3712, 3722, 3725, 3862, 4065, 4269, 4284, 4380, 4599, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,2,1],[2,3,2,3]]», by decideFin!⟩
