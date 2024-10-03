import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2696,2812] [2441,2446,2456,2506,2530,2533,2543,2554,2659,2687,2709,2724,2770,2791,2836,3253,3258,3268,3278,3288,3664,3674,3677,3694,3749,4065,4272,4351] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]», by decideFin!⟩
