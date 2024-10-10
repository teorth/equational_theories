
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[4,2,3,4,0],[4,4,1,2,1],[4,2,4,2,2],[4,2,3,4,3],[4,4,4,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[4,2,3,4,0],[4,4,1,2,1],[4,2,4,2,2],[4,2,3,4,3],[4,4,4,4,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[4,2,3,4,0],[4,4,1,2,1],[4,2,4,2,2],[4,2,3,4,3],[4,4,4,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[4,2,3,4,0],[4,4,1,2,1],[4,2,4,2,2],[4,2,3,4,3],[4,4,4,4,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [434] [1023] :=
    ⟨Fin 5, «FinitePoly [[4,2,3,4,0],[4,4,1,2,1],[4,2,4,2,2],[4,2,3,4,3],[4,4,4,4,4]]», by decideFin!⟩
