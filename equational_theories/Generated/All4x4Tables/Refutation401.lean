
import equational_theories.AllEquations
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
  ∃ (G : Type) (_ : Magma G), Facts G [426] [8, 99, 359, 413, 414, 427, 429, 430, 436, 437, 439, 440, 817, 1020, 1025, 1028, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1049, 1223, 1832, 1857, 1860, 1861, 3253, 3659, 3862, 4065, 4131, 4269, 4270, 4314, 4318, 4583, 4598, 4631, 4673] :=
    ⟨Fin 4, «FinitePoly [[2,2,0,3],[2,3,1,0],[2,2,1,2],[2,0,3,1]]», by decideFin!⟩
