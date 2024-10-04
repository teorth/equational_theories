
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[3,2,0,1],[3,2,0,1],[3,2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[3,2,0,1],[3,2,0,1],[3,2,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[3,2,0,1],[3,2,0,1],[3,2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[3,2,0,1],[3,2,0,1],[3,2,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [608] [99, 151, 817, 1020, 1223, 1629, 1832, 2035, 3253, 3659] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[3,2,0,1],[3,2,0,1],[3,2,0,1]]», by decideFin!⟩
