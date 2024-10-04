
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,1,1],[2,2,2,2],[0,0,0,0],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,1,1],[2,2,2,2],[0,0,0,0],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,1,1],[2,2,2,2],[0,0,0,0],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,1,1],[2,2,2,2],[0,0,0,0],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [38, 269] [3, 8, 23, 47, 99, 151, 203, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2238, 2441, 3050, 3659, 3862, 4065, 4272, 4273, 4275, 4276, 4290, 4291, 4293, 4320, 4321, 4343, 4380] :=
    ⟨Fin 4, «FinitePoly [[1,1,1,1],[2,2,2,2],[0,0,0,0],[3,3,3,3]]», by decideFin!⟩
