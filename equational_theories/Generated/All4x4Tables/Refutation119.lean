
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1,0],[1,1,1,0],[1,2,2,1],[2,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1,0],[1,1,1,0],[1,2,2,1],[2,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,1,0],[1,1,1,0],[1,2,2,1],[2,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1,0],[1,1,1,0],[1,2,2,1],[2,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [9, 824] [102, 429, 825, 826, 1026, 1029, 1039, 1226, 1228, 1229, 1231, 1232, 1632, 1850, 2051, 2449, 3459, 3511, 3518, 3519, 3521, 3721, 3725, 3917, 3924, 3927, 3928, 4120, 4121, 4127, 4131, 4314, 4398, 4472, 4473, 4598, 4599, 4673] :=
    ⟨Fin 4, «FinitePoly [[0,0,1,0],[1,1,1,0],[1,2,2,1],[2,3,3,3]]», by decideFin!⟩
