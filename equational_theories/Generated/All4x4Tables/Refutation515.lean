
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,2,3],[2,1,2,3],[0,1,2,0],[0,1,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,2,3],[2,1,2,3],[0,1,2,0],[0,1,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,2,3],[2,1,2,3],[0,1,2,0],[0,1,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,2,3],[2,1,2,3],[0,1,2,0],[0,1,1,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2716, 3108] [1041, 1055, 1958, 2296, 2310, 2314, 2318, 2347, 2364, 2368, 2372, 2381, 2398, 2584, 2665, 2669, 2699, 2739, 3529, 3749, 3883, 3897, 4362] :=
    ⟨Fin 4, «FinitePoly [[0,2,2,3],[2,1,2,3],[0,1,2,0],[0,1,1,3]]», Finite.of_fintype _, by decideFin!⟩
