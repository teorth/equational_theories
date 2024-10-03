import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,0,1],[3,2,1,0],[0,1,2,3],[2,0,3,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,0,1],[3,2,1,0],[0,1,2,3],[2,0,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,0,1],[3,2,1,0],[0,1,2,3],[2,0,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,0,1],[3,2,1,0],[0,1,2,3],[2,0,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1722,2644,2737,3050,3143,3152] [1658,1695,1729,1898,2101,2238,2304,2441,2543,2699,2710,3068,3306,4435] :=
    ⟨Fin 4, «FinitePoly [[1,3,0,1],[3,2,1,0],[0,1,2,3],[2,0,3,2]]», by decideFin!⟩
