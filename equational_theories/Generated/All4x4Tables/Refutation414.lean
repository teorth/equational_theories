
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,2,1],[3,3,3,3],[3,3,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,2,1],[3,3,3,3],[3,3,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,2,1],[3,3,3,3],[3,3,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,2,1],[3,3,3,3],[3,3,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3470] [3253, 3509, 3519, 3521, 3522, 3659, 4065, 4269, 4270, 4380] :=
    ⟨Fin 4, «FinitePoly [[1,2,2,1],[3,3,3,3],[3,3,3,3],[3,3,3,3]]», by decideFin!⟩
