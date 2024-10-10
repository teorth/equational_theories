
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,3],[0,1,2,3],[3,1,2,0],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,3],[0,1,2,3],[3,1,2,0],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,1,3],[0,1,2,3],[3,1,2,0],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,3],[0,1,2,3],[3,1,2,0],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [679, 916, 1518, 2063] [632, 669, 825, 879, 1444, 1451, 2043, 3880, 3925, 3952, 3955, 4073, 4083, 4128, 4131, 4158, 4165, 4606, 4635] :=
    ⟨Fin 4, «FinitePoly [[0,2,1,3],[0,1,2,3],[3,1,2,0],[0,1,2,3]]», by decideFin!⟩
