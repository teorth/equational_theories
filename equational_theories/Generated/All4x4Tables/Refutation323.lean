
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2089] [1426, 2051, 2124, 3456, 3877, 3880, 3915, 3918, 3952, 3955, 4314, 4606, 4666] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]», by decideFin!⟩
