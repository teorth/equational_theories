
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3681, 4417] [3671, 3680, 3702, 4436, 4605, 4629, 4635, 4656, 4658, 4666] :=
    ⟨Fin 4, «FinitePoly [[3,0,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]», by decideFin!⟩
