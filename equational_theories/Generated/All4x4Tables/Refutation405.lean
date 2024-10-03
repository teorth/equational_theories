import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[3,0,0,3],[3,2,1,3],[0,1,2,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,3],[3,0,0,3],[3,2,1,3],[0,1,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,3],[3,0,0,3],[3,2,1,3],[0,1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,3],[3,0,0,3],[3,2,1,3],[0,1,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2472] [203,205,211,2238,2240,2243,2246,2249,2256,2456,2459,2462,4065,4068,4070,4128,4270,4341] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,3],[3,0,0,3],[3,2,1,3],[0,1,2,0]]», by decideFin!⟩
