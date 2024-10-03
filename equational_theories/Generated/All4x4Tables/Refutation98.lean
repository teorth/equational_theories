import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,3],[3,3,3,2],[1,0,3,3],[3,0,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,3],[3,3,3,2],[1,0,3,3],[3,0,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,3],[3,3,3,2],[1,0,3,3],[3,0,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,3],[3,3,3,2],[1,0,3,3],[3,0,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3475,3496] [307,309,310,312,313,316,319,320,323,3261,3306,3458,3467,3478,3482,3488,3492,3504,3522,3664,3668,3672,3674,3678,3682,3694,3699,3704,3709,4065,4084,4118] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,3],[3,3,3,2],[1,0,3,3],[3,0,3,3]]», by decideFin!⟩
