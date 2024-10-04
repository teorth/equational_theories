import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0,1],[1,1,0,1],[2,0,2,2],[2,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0,1],[1,1,0,1],[2,0,2,2],[2,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,0,1],[1,1,0,1],[2,0,2,2],[2,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0,1],[1,1,0,1],[2,0,2,2],[2,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [428,1027] [103,106,825,827,828,829,830,831,833,834,838,839,840,841,1030,1032,1033,1034,1037,1227,1230,1233,1235,1236,1237,1240,1243,1245,1246,1247,1250,1259,1260,1261,1633,1636,2452,2462,3460,3463,3724,3726,3727,3931,4673] :=
    ⟨Fin 4, «FinitePoly [[0,0,0,1],[1,1,0,1],[2,0,2,2],[2,3,3,3]]», by decideFin!⟩
