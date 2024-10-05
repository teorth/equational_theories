
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,4,2,0,2,2],[3,3,3,3,3,3],[4,2,4,4,4,0],[5,5,5,5,5,5],[0,0,0,2,0,4],[1,1,1,1,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,4,2,0,2,2],[3,3,3,3,3,3],[4,2,4,4,4,0],[5,5,5,5,5,5],[0,0,0,2,0,4],[1,1,1,1,1,1]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[2,4,2,0,2,2],[3,3,3,3,3,3],[4,2,4,4,4,0],[5,5,5,5,5,5],[0,0,0,2,0,4],[1,1,1,1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,4,2,0,2,2],[3,3,3,3,3,3],[4,2,4,4,4,0],[5,5,5,5,5,5],[0,0,0,2,0,4],[1,1,1,1,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2656] [261, 263, 2043, 2044, 2051, 2060, 2061, 2660, 2669, 2672, 2856, 2863, 2873, 3315, 3316, 3318, 3319, 3518, 3519, 3521, 3522, 4598, 4656] :=
    ⟨Fin 6, «FinitePoly [[2,4,2,0,2,2],[3,3,3,3,3,3],[4,2,4,4,4,0],[5,5,5,5,5,5],[0,0,0,2,0,4],[1,1,1,1,1,1]]», by decideFin!⟩
