
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3,4],[2,3,1,4,0],[3,0,4,2,1],[4,2,0,1,3],[1,4,3,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3,4],[2,3,1,4,0],[3,0,4,2,1],[4,2,0,1,3],[1,4,3,0,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,1,2,3,4],[2,3,1,4,0],[3,0,4,2,1],[4,2,0,1,3],[1,4,3,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3,4],[2,3,1,4,0],[3,0,4,2,1],[4,2,0,1,3],[1,4,3,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [167, 2244, 2291, 3201] [40, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2246, 2256, 2441, 2644, 2847, 3058, 3066, 3075, 3253, 3456, 3862, 4065, 4268, 4273, 4283, 4314, 4585, 4587, 4606] :=
    ⟨Fin 5, «FinitePoly [[0,1,2,3,4],[2,3,1,4,0],[3,0,4,2,1],[4,2,0,1,3],[1,4,3,0,2]]», by decideFin!⟩
