import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,3],[0,1,2,3],[0,1,2,3],[1,0,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,3],[0,1,2,3],[0,1,2,3],[1,0,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,1,3],[0,1,2,3],[0,1,2,3],[1,0,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,3],[0,1,2,3],[0,1,2,3],[1,0,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1353,1370,2115,2203] [104,166,429,473,562,1228,1248,1258,2050,2124,2161,3867,3877,3897,4320,4362,4587,4666] :=
    ⟨Fin 4, «FinitePoly [[0,2,1,3],[0,1,2,3],[0,1,2,3],[1,0,2,3]]», by decideFin!⟩
