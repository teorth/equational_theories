
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,1,1],[3,3,1,1],[0,1,2,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,1,1],[3,3,1,1],[0,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,1,1],[3,3,1,1],[0,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,1,1],[3,3,1,1],[0,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2592, 2808, 2964, 2998, 3214] [411, 1020, 1832, 4362] :=
    ⟨Fin 4, «FinitePoly [[3,2,1,1],[3,3,1,1],[0,1,2,3],[0,1,2,3]]», by decideFin!⟩
