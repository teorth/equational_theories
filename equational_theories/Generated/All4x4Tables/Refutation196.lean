import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,3,1],[3,1,0,3],[1,2,1,0],[2,3,2,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,3,1],[3,1,0,3],[1,2,1,0],[2,3,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,3,1],[3,1,0,3],[1,2,1,0],[2,3,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,3,1],[3,1,0,3],[1,2,1,0],[2,3,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [655,658] [417,419,427,429,452,455,617,639,647,825,833,861,1023,1026,1038,1045,1053,1061,1223,1226,1229,1231,1239,1241,1248,1252,1256,1264,1267,4598] :=
    ⟨Fin 4, «FinitePoly [[1,0,3,1],[3,1,0,3],[1,2,1,0],[2,3,2,1]]», by decideFin!⟩
