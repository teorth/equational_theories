
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [58] [411, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3456, 3661, 3722, 3862, 4118, 4121, 4128, 4380, 4599] :=
    ⟨Fin 4, «FinitePoly [[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]», by decideFin!⟩
