import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,2,3],[3,3,3,3],[2,0,0,2],[1,1,1,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,2,3],[3,3,3,3],[2,0,0,2],[1,1,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,2,3],[3,3,3,3],[2,0,0,2],[1,1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,2,3],[3,3,3,3],[2,0,0,2],[1,1,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1645] [1647,1654,1658,1662,1670,1673,2444,2447,2457,2459,2466,2470,2474,2482,2485,3053,3056,3066,3068,3075,3079,3083,3091,3094,3253,3261,3306,3319,3334,4585,4598,4656,4673] :=
    ⟨Fin 4, «FinitePoly [[0,2,2,3],[3,3,3,3],[2,0,0,2],[1,1,1,0]]», by decideFin!⟩
