import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [109,427,849,851,1060,1257] [105,429,430,432,433,434,437,439,442,443,832,833,834,836,837,838,839,840,841,854,1022,1031,1035,1038,1041,1046,1048,1051,1055,1059,1063,1067,1229,1231,1234,1242,1243,1244,1264,1266,1270,1834,1847,1850,1853,3255,3316,3322,3724,3864,3925,3935,4131,4269,4316] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]», by decideFin!⟩
