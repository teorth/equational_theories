import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,1],[1,2,0,0],[2,2,2,2],[2,2,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,1],[1,2,0,0],[2,2,2,2],[2,2,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,1],[1,2,0,0],[2,2,2,2],[2,2,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,1],[1,2,0,0],[2,2,2,2],[2,2,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [50,615,624] [359,360,361,616,626,3660,3661,3862,3864,4065] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,1],[1,2,0,0],[2,2,2,2],[2,2,3,3]]», by decideFin!⟩
