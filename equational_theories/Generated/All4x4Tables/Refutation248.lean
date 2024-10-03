import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0,1],[1,1,1,2],[2,2,0,3],[3,3,1,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0,1],[1,1,1,2],[2,2,0,3],[3,3,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,0,1],[1,1,1,2],[2,2,0,3],[3,3,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0,1],[1,1,1,2],[2,2,0,3],[3,3,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [100,821,847,1052] [105,107,1223,1224,1225,1226,1228,1238,1239,1241,1242,1243,1248,1249,1250,1251,1252,1253,1254,1255,1262,1263,4598] :=
    ⟨Fin 4, «FinitePoly [[0,0,0,1],[1,1,1,2],[2,2,0,3],[3,3,1,0]]», by decideFin!⟩
