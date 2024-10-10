
import equational_theories.Equations.All
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
  ∃ (G : Type) (_ : Magma G), Facts G [1229] [99, 411, 817, 1020, 1238, 1239, 1241, 1242, 1248, 1249, 1251, 1252, 1832, 3253, 3862, 4065, 4269, 4631] :=
    ⟨Fin 4, «FinitePoly [[0,0,1,3],[3,1,3,1],[3,1,0,2],[1,3,1,3]]», by decideFin!⟩
