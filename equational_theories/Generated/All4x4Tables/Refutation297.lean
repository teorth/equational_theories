import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[2,1,0,3],[3,1,2,0],[1,0,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[2,1,0,3],[3,1,2,0],[1,0,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[2,1,0,3],[3,1,2,0],[1,0,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[2,1,0,3],[3,1,2,0],[1,0,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [879,1315] [104,138,166,194,872,1228,1238,1248,1258,1288,1299,1336,1353,1370,1387,1405,2050,2063,2078,2087,2115,2124,2152,2161,2182,2203,2227,4073,4131,4146] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[2,1,0,3],[3,1,2,0],[1,0,2,3]]», by decideFin!⟩
