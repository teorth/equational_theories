
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,4,5,0,1],[2,3,0,5,4,1],[2,3,4,5,0,1],[4,3,2,5,0,1],[2,3,4,5,0,1],[0,3,4,5,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,3,4,5,0,1],[2,3,0,5,4,1],[2,3,4,5,0,1],[4,3,2,5,0,1],[2,3,4,5,0,1],[0,3,4,5,2,1]]» : Magma (Fin 6) where
  op := finOpTable "[[2,3,4,5,0,1],[2,3,0,5,4,1],[2,3,4,5,0,1],[4,3,2,5,0,1],[2,3,4,5,0,1],[0,3,4,5,2,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,3,4,5,0,1],[2,3,0,5,4,1],[2,3,4,5,0,1],[4,3,2,5,0,1],[2,3,4,5,0,1],[0,3,4,5,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [960] [55, 65, 669, 676, 679, 713, 825, 845, 872, 882, 1434, 1451, 1491, 1525, 3915, 3925, 3952, 3962, 4118, 4128, 4155, 4165, 4275, 4320] :=
    ⟨Fin 6, «All4x4Tables [[2,3,4,5,0,1],[2,3,0,5,4,1],[2,3,4,5,0,1],[4,3,2,5,0,1],[2,3,4,5,0,1],[0,3,4,5,2,1]]», Finite.of_fintype _, by decideFin!⟩
