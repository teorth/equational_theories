import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,3],[3,3,3,3],[0,1,0,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,1,3],[3,3,3,3],[0,1,0,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,3],[3,3,3,3],[0,1,0,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,3],[3,3,3,3],[0,1,0,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2709] [2441,2443,2446,2449,2452,2456,2459,2462,2466,2469,2472,2476,2480,2484,2488,2496,2517,2530,2533,2536,2543,2554,2558,2571,2605,2623,2646,2652,2659,2736,3142,3261,3278,3659,3749,4131] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,3],[3,3,3,3],[0,1,0,3],[0,1,2,3]]», by decideFin!⟩
