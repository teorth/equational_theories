import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,2,4,1,0],[4,3,1,0,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,2,4,1,0],[4,3,1,0,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,2,4,1,0],[4,3,1,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,2,4,1,0],[4,3,1,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [825,861,1793] [8,11,23,26,411,414,417,419,427,429,436,440,444,452,455,473,513,562,614,617,620,622,630,632,639,643,647,655,658,820,823,835,842,850,858,1020,1023,1026,1028,1036,1038,1045,1049,1053,1061,1064,1223,1226,1229,1231,1239,1241,1248,1252,1256,1264,1267,1832,1835,1857,1861,1865,3253,3256,3315,3319,3323,3659,3662,3721,3725,3729,3862,3870,3915,3928,3943,4270,4341,4598] :=
    ⟨Fin 5, «FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,2,4,1,0],[4,3,1,0,2]]», by decideFin!⟩
