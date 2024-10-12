
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,3],[3,3,0,3],[1,3,1,3],[0,3,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,3],[3,3,0,3],[1,3,1,3],[0,3,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,3],[3,3,0,3],[1,3,1,3],[0,3,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,3],[3,3,0,3],[1,3,1,3],[0,3,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3893, 4093] [3870, 3877, 4067, 4070, 4080, 4090, 4269, 4599, 4606, 4622, 4635, 4666] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,3],[3,3,0,3],[1,3,1,3],[0,3,1,3]]», by decideFin!⟩
