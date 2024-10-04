
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,1],[1,1,1,1],[2,2,1,0],[3,3,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,1],[1,1,1,1],[2,2,1,0],[3,3,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,1],[1,1,1,1],[2,2,1,0],[3,3,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,1],[1,1,1,1],[2,2,1,0],[3,3,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [105, 837, 846, 1051, 1224, 1225, 1228, 1239, 1252] [8, 100, 104, 108, 359, 411, 819, 820, 823, 832, 833, 842, 843, 845, 1025, 1028, 1035, 1036, 1038, 1039, 1049, 1226, 1229, 1231, 1238, 1242, 1249, 1832, 3255, 3256, 3316, 3318, 3319, 3659, 3862, 4065, 4131, 4269, 4598, 4631, 4673] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,1],[1,1,1,1],[2,2,1,0],[3,3,2,2]]», by decideFin!⟩
