import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,1],[3,3,0,0],[2,2,2,0],[2,1,1,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,1,1],[3,3,0,0],[2,2,2,0],[2,1,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,1],[3,3,0,0],[2,2,2,0],[2,1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,1],[3,3,0,0],[2,2,2,0],[2,1,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1834,1837,1843] [151,153,156,159,162,1629,1631,1634,1637,1640,1644,1647,1650,1654,1657,1660,1664,1668,1672,1676,1847,1850,1853,1857,1860,1863,1867,1871,1875,1879,3253,3255,3258,3261,3264,3306,3309,3312,3316,3319,3322,3326,3330,3334,3338,4065,4067,4070,4073,4076,4118,4121,4124,4128,4131,4134,4138,4142,4146,4150,4269,4284,4287,4316,4340,4360,4584,4599,4602,4631,4655,4675] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,1],[3,3,0,0],[2,2,2,0],[2,1,1,1]]», by decideFin!⟩
