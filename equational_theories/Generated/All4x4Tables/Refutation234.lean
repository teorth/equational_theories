
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,3,1],[2,1,1,2],[2,2,1,2],[2,3,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,3,1],[2,1,1,2],[2,2,1,2],[2,3,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,3,1],[2,1,1,2],[2,2,1,2],[2,3,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,3,1],[2,1,1,2],[2,2,1,2],[2,3,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [443] [99, 426, 429, 436, 819, 832, 833, 836, 842, 843, 845, 1020, 1223, 1832, 3253, 3659, 3864, 3865, 3867, 3915, 3925, 4065, 4269, 4270, 4314, 4583, 4598, 4631] :=
    ⟨Fin 4, «FinitePoly [[2,0,3,1],[2,1,1,2],[2,2,1,2],[2,3,3,1]]», by decideFin!⟩
