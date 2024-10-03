import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [826] [3,4,8,9,10,11,12,23,24,25,26,27,38,42,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,620,633,833,1426,1435,1445,1452,3050,3056,3068,3079,3091,3867,3925,3935,4070,4128,4130,4138,4399] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]», by decideFin!⟩
