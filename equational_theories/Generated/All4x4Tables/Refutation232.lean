
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,3,1],[3,3,3,3],[0,0,0,0],[2,0,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,3,1],[3,3,3,3],[0,0,0,0],[2,0,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,3,1],[3,3,3,3],[0,0,0,0],[2,0,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,3,1],[3,3,3,3],[0,0,0,0],[2,0,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2052] [3461, 3462, 3521, 3522, 3862, 4268, 4606, 4666] :=
    ⟨Fin 4, «FinitePoly [[3,3,3,1],[3,3,3,3],[0,0,0,0],[2,0,2,0]]», by decideFin!⟩
