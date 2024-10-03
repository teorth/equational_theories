import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,3,3],[3,2,0,3],[0,3,3,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,3,3],[3,2,0,3],[0,3,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,3,3],[3,2,0,3],[0,3,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,3,3],[3,2,0,3],[0,3,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2736] [203,211,221,2238,2243,2246,2253,2256,2266,2277,2281,2293,2340,2456,2484,2662,2696,2746,2778,4065] :=
    ⟨Fin 4, «FinitePoly [[1,1,3,3],[3,2,0,3],[0,3,3,3],[0,1,2,3]]», by decideFin!⟩
