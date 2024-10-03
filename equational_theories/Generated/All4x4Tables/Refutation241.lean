import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1,3],[3,3,3,3],[1,1,1,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1,3],[3,3,3,3],[1,1,1,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,1,3],[3,3,3,3],[1,1,1,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1,3],[3,3,3,3],[1,1,1,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2533,2709] [23,25,31,203,205,208,211,214,218,221,224,231,242,246,309,1629,1631,1637,1644,1647,1650,1657,1672,1718,1721,1724,1731,1746,2240,2249,2259,2269,2273,2277,2285,2296,2300,2306,2310,2314,2322,2333,2351,2372,2376,2389,2420,2425,3050,3058,3456,3522,4065,4118] :=
    ⟨Fin 4, «FinitePoly [[0,1,1,3],[3,3,3,3],[1,1,1,3],[0,1,2,3]]», by decideFin!⟩
