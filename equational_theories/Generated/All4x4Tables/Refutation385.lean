
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,0,3],[2,3,1,0],[2,2,1,2],[2,0,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,0,3],[2,3,1,0],[2,2,1,2],[2,0,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,0,3],[2,3,1,0],[2,2,1,2],[2,0,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,0,3],[2,3,1,0],[2,2,1,2],[2,0,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [426] [99, 413, 429, 436, 437, 440, 817, 1020, 1223, 1832, 3253, 3659, 3862, 4065, 4269, 4270, 4314, 4583, 4598, 4631] :=
    ⟨Fin 4, «FinitePoly [[2,2,0,3],[2,3,1,0],[2,2,1,2],[2,0,3,1]]», by decideFin!⟩
