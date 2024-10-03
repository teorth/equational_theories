import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2,3],[2,2,2,3],[0,1,2,2],[0,1,1,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,2,3],[2,2,2,3],[0,1,2,2],[0,1,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,2,3],[2,2,2,3],[0,1,2,2],[0,1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,2,3],[2,2,2,3],[0,1,2,2],[0,1,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2702,2733,2739] [218,221,224,2290,2293,2296,2300,2303,2306,2310,2314,2318,2322,2327,2330,2333,2364,2368,2372,2376,2530,2659,2662,2665,2770,2774,2778,2782,3461,3464,3664,3712,3769,3786,4320] :=
    ⟨Fin 4, «FinitePoly [[0,0,2,3],[2,2,2,3],[0,1,2,2],[0,1,1,0]]», by decideFin!⟩
