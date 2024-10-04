
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,3,3],[1,1,2,1],[1,1,2,1],[0,0,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,3,3],[1,1,2,1],[1,1,2,1],[0,0,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,3,3],[1,1,2,1],[1,1,2,1],[0,0,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,3,3],[1,1,2,1],[1,1,2,1],[0,0,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [25, 101, 156, 266, 1234, 1441, 2070, 3097] [107, 108, 413, 436, 819, 845, 1045, 1224, 1226, 1229, 1239, 1241, 1242, 1248, 1249, 1251, 1252, 1451, 1454, 1634, 1637, 1654, 1657, 1840, 1850, 1860, 2037, 2043, 2053, 2063, 3255, 3256, 3258, 3259, 3261, 3262, 3316, 3459, 3461, 3464, 3512, 3662, 3665, 3668, 3928, 4068, 4121, 4269, 4270, 4314, 4599, 4655] :=
    ⟨Fin 4, «FinitePoly [[0,3,3,3],[1,1,2,1],[1,1,2,1],[0,0,3,3]]», by decideFin!⟩
