
import equational_theories.AllEquations
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
  ∃ (G : Type) (_ : Magma G), Facts G [65, 72, 679, 723, 916, 947, 1370, 1506, 1518, 2203] [117, 138, 159, 385, 632, 653, 669, 676, 825, 879, 882, 960, 1278, 1299, 1315, 1387, 1444, 1451, 1481, 1560, 2043, 2078, 2100, 2152, 2182, 3880, 3925, 3952, 3955, 3972, 3989, 3997, 4006, 4073, 4083, 4128, 4131, 4158, 4165, 4226, 4606, 4635] :=
    ⟨Fin 4, «FinitePoly [[0,2,1,3],[0,1,2,3],[3,1,2,0],[0,1,2,3]]», by decideFin!⟩
