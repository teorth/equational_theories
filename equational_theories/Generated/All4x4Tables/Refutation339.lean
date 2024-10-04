import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[1,0,0,0],[2,2,0,0],[3,2,0,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[1,0,0,0],[2,2,0,0],[3,2,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[1,0,0,0],[2,2,0,0],[3,2,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[1,0,0,0],[2,2,0,0],[3,2,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [647,1523,2132] [1023,1026,1038,1045,1053,1061,1229,1231,1239,1241,1264,1267,1481,2090,3549,3955,4598] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[1,0,0,0],[2,2,0,0],[3,2,0,0]]», by decideFin!⟩
