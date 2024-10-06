
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[2,0,1,3],[1,2,0,3],[1,2,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[2,0,1,3],[1,2,0,3],[1,2,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[2,0,1,3],[1,2,0,3],[1,2,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[2,0,1,3],[1,2,0,3],[1,2,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1082, 1109, 1887, 2706, 3481, 3677] [411, 614, 817, 1028, 1038, 1045, 1075, 1122, 1223, 1426, 1654, 1684, 1691, 1731, 1840, 1894, 1921, 2035, 2238, 2449, 2459, 2496, 2733, 2847, 3058, 3075, 3112, 3139, 3253, 3464, 3509, 3549, 3556, 3684, 3880, 4073, 4083, 4090, 4158, 4275, 4622, 4635] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[2,0,1,3],[1,2,0,3],[1,2,0,3]]», by decideFin!⟩
