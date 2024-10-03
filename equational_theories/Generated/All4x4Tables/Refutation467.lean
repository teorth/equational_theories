import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,1],[3,0,3,1],[3,2,0,1],[3,0,3,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,3,1],[3,0,3,1],[3,2,0,1],[3,0,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,3,1],[3,0,3,1],[3,2,0,1],[3,0,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,3,1],[3,0,3,1],[3,2,0,1],[3,0,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [629,642,657] [47,49,52,55,58,359,361,375,378,381,616,625,632,635,639,645,649,653,661,817,819,822,825,828,832,835,838,842,845,848,852,856,860,864,1426,1428,1431,1434,1437,1441,1444,1447,1451,1454,1457,1461,1465,1469,1473,3862,3864,3867,3870,3873,3915,3918,3921,3925,3928,3931,3935,3939,3943,3947,4065,4067,4070,4073,4076,4118,4121,4124,4128,4131,4134,4138,4142,4146,4150,4269,4284,4287,4316,4340,4360,4584,4599,4602,4631,4655,4675] :=
    ⟨Fin 4, «FinitePoly [[3,0,3,1],[3,0,3,1],[3,2,0,1],[3,0,3,1]]», by decideFin!⟩
