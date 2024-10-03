import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[2,3,2,3],[2,3,2,1],[0,1,2,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,3],[2,3,2,3],[2,3,2,1],[0,1,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,3],[2,3,2,3],[2,3,2,1],[0,1,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,3],[2,3,2,3],[2,3,2,1],[0,1,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1437,1441,1447,2273] [1451,1454,1457,1461,1465,1469,1473,4070,4073,4076,4121,4124,4128,4134,4138,4142,4146,4150,4287,4340,4360,4584,4599,4602,4631,4655,4675] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,3],[2,3,2,3],[2,3,2,1],[0,1,2,1]]», by decideFin!⟩
