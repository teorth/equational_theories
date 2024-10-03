import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,3,3],[2,3,0,3],[0,1,2,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,3,3],[2,3,0,3],[0,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,3,3],[2,3,0,3],[0,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,3,3],[2,3,0,3],[0,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2571,2724] [2446,2554,2659,2687,2770,2791,2836,3258,3261,3268,3278,3288,3458,3664,3674,3677,3694,3749,4272,4351] :=
    ⟨Fin 4, «FinitePoly [[2,1,3,3],[2,3,0,3],[0,1,2,3],[0,1,2,3]]», by decideFin!⟩
