import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,1,3],[3,0,2,1],[2,1,3,0],[0,2,3,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,1,3],[3,0,2,1],[2,1,3,0],[0,2,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,1,3],[3,0,2,1],[2,1,3,0],[0,2,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,1,3],[3,0,2,1],[2,1,3,0],[0,2,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2743,2847] [3,5,8,10,13,16,19,23,25,28,31,34,39,45,99,117,411,429,473,513,562,1721,1897,2035,2100,2127,2134,2699,2909,2939,3068,4283,4358,4598,4673] :=
    ⟨Fin 4, «FinitePoly [[2,0,1,3],[3,0,2,1],[2,1,3,0],[0,2,3,1]]», by decideFin!⟩
