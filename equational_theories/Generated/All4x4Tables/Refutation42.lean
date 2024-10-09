
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,2,3],[3,2,2,3],[1,0,1,0],[1,0,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,2,3],[3,2,2,3],[1,0,1,0],[1,0,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,2,3],[3,2,2,3],[1,0,1,0],[1,0,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,2,3],[3,2,2,3],[1,0,1,0],[1,0,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [162, 4142] [3255, 3256, 3262, 3315, 3318, 3319, 3457, 3459, 3465, 3518, 3521, 4066, 4068, 4071, 4120, 4127, 4268, 4269, 4270, 4283, 4314, 4583, 4598, 4629, 4656] :=
    ⟨Fin 4, «FinitePoly [[3,2,2,3],[3,2,2,3],[1,0,1,0],[1,0,1,0]]», by decideFin!⟩
