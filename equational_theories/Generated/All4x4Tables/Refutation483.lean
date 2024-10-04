import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[4,3,1,0,2],[3,2,4,1,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[4,3,1,0,2],[3,2,4,1,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[4,3,1,0,2],[3,2,4,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[4,3,1,0,2],[3,2,4,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1455,1459,1523,1658,2038,2132,2254,2267,2282,2470] [3050,3053,3056,3058,3066,3068,3075,3079,3083,3091,3094,3456,3459,3464,3472,3485,3500,3518,3522,3526,3862,3870,3878,3891,3906,4585,4598,4656,4673] :=
    ⟨Fin 5, «FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[4,3,1,0,2],[3,2,4,1,0]]», by decideFin!⟩
