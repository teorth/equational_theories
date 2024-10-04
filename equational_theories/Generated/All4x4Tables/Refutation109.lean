
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,0,1],[2,2,1,1],[2,2,2,2],[1,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,0,1],[2,2,1,1],[2,2,2,2],[1,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,0,1],[2,2,1,1],[2,2,2,2],[1,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,0,1],[2,2,1,1],[2,2,2,2],[1,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [832, 833, 846, 1244, 1250, 1253, 1255] [8, 100, 105, 359, 411, 818, 819, 820, 823, 842, 843, 845, 1020, 1025, 1028, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1049, 1226, 1229, 1231, 1239, 1242, 1832, 1863, 1865, 3256, 3306, 3315, 3316, 3319, 3659, 3864, 3915, 3925, 4065, 4131, 4269, 4270, 4583, 4631] :=
    ⟨Fin 4, «FinitePoly [[1,3,0,1],[2,2,1,1],[2,2,2,2],[1,3,3,2]]», by decideFin!⟩
