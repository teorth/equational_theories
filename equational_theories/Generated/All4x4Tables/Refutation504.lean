import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,0,4],[0,3,1,4,2],[2,0,4,3,1],[4,1,0,2,3],[3,4,2,1,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,0,4],[0,3,1,4,2],[2,0,4,3,1],[4,1,0,2,3],[3,4,2,1,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,3,0,4],[0,3,1,4,2],[2,0,4,3,1],[4,1,0,2,3],[3,4,2,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,0,4],[0,3,1,4,2],[2,0,4,3,1],[4,1,0,2,3],[3,4,2,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [826,3113] [3,8,47,65,73,99,102,117,125,151,160,167,203,212,229,255,258,263,307,326,335,359,362,375,614,617,632,640,679,704,1020,1029,1046,1076,1085,1110,1119,1223,1226,1231,1278,1323,1426,1455,1482,1491,1518,1526,2035,2044,2053,2060,2100,2125,2238,2267,2294,2300,2328,2330,2644,2653,2663,2672,2699,2744,2847,2850,2863,2875,2910,2939,3253,3271,3279,3319,3343,3352,3659,3668,3675,3715,3722,3761,3862,3871,3888,3915,3924,3954,4380,4383,4408,4435,4443,4470] :=
    ⟨Fin 5, «FinitePoly [[1,2,3,0,4],[0,3,1,4,2],[2,0,4,3,1],[4,1,0,2,3],[3,4,2,1,0]]», by decideFin!⟩
