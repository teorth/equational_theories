
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,4,2,0],[1,2,4,2,0],[3,2,4,2,0],[3,2,4,2,0],[3,2,4,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,4,2,0],[1,2,4,2,0],[3,2,4,2,0],[3,2,4,2,0],[3,2,4,2,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,4,2,0],[1,2,4,2,0],[3,2,4,2,0],[3,2,4,2,0],[3,2,4,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,4,2,0],[1,2,4,2,0],[3,2,4,2,0],[3,2,4,2,0],[3,2,4,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [454] [3862] :=
    ⟨Fin 5, «FinitePoly [[1,2,4,2,0],[1,2,4,2,0],[3,2,4,2,0],[3,2,4,2,0],[3,2,4,2,0]]», by decideFin!⟩
