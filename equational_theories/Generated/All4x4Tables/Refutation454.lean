import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,1,1],[3,3,0,1],[3,1,0,1],[2,3,1,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,1,1],[3,3,0,1],[3,1,0,1],[2,3,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,1,1],[3,3,0,1],[3,1,0,1],[2,3,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,1,1],[3,3,0,1],[3,1,0,1],[2,3,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1921] [411,419,429,436,466,473,500,513,528,562,575,1020,1028,1038,1045,1075,1082,1109,1122,1137,1171,1184,1840,1850,1857,1887,1894,1934,1949,1983,1996,4275,4307,4320,4362] :=
    ⟨Fin 4, «FinitePoly [[2,3,1,1],[3,3,0,1],[3,1,0,1],[2,3,1,1]]», by decideFin!⟩
