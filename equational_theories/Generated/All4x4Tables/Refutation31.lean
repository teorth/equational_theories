
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1,3],[3,1,3,1],[3,1,0,2],[1,3,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1,3],[3,1,3,1],[3,1,0,2],[1,3,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,1,3],[3,1,3,1],[3,1,0,2],[1,3,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1,3],[3,1,3,1],[3,1,0,2],[1,3,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1229] [8, 99, 359, 411, 817, 1020, 1025, 1028, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1049, 1224, 1225, 1226, 1228, 1231, 1238, 1239, 1241, 1242, 1248, 1249, 1251, 1252, 1832, 1857, 1860, 1861, 3253, 3862, 4065, 4131, 4269, 4598, 4631] :=
    ⟨Fin 4, «FinitePoly [[0,0,1,3],[3,1,3,1],[3,1,0,2],[1,3,1,3]]», by decideFin!⟩
